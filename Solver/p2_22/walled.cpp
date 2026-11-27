// Solver WALLED - Kelompok P2_22 (Paralel 2, Analisis Algoritme IPB University)
//
// Tembok memecah setiap baris, kolom dan diagonal menjadi segmen; dua ratu saling serang hanya jika berada di segmen
// yang sama. Jadi masalahnya: pilih sel sebanyak mungkin sehingga setiap segmen (4 arah) memuat paling banyak 1 ratu,
// lalu kembalikan SEMUA papan dengan jumlah ratu maksimum. Algoritme hibrida:
//
//   1. Branch & Bound baris demi baris, segmen demi segmen, dengan mask kolom/diagonal sebagai register geser: mask
//      digeser ke baris berikutnya lalu bit yang terkena tembok dihapus (serangan berhenti di tembok).
//   2. Russian Doll Search per segmen: optimum sub-papan "segmen j sampai akhir" dihitung dari belakang ke depan.
//      Nilai itu menjadi batas atas yang sangat ketat untuk pencarian berikutnya, dan setiap sub-pencarian hanya perlu
//      menjawab "bisakah satu ratu lebih banyak?". Batas atas juga memakai jumlah segmen kolom/diagonal yang masih bebas.
//   3. Enumerasi semua papan optimum: B&B dengan anggaran node. Jika anggaran habis (papan dengan banyak tembok),
//      pindah ke Dynamic Programming per baris: state = (mask kolom, d1, d2) di batas baris, maju menghitung g, mundur
//      menghitung h (sisa maksimum eksak), lalu hanya jalur dengan g + h = optimum yang ditelusuri.
//
// Tanpa variabel global: semua state ada di struct yang dibuat di dalam solveWalled(). Tabel DP (heap) hanya dibuat
// bila DP dipakai (8 + ~6 byte per state) dan dilepas sebelum hasil dibangun. Papan ditampung dulu di buffer lokal
// 1 byte per ratu, lalu hasil akhir dibuat dengan reserve() yang pas.
//
// kUseDp = false -> tanpa DP sama sekali: heap paling kecil (hanya hasil), tetapi papan sulit bisa ~3x lebih lambat.
#include <cstdint>
#include <cstring>
#include <string>
#include <utility>
#include <vector>

#include "nqueens.h"

namespace {

constexpr int kMaxN = 16;
constexpr int kMaxSeg = kMaxN * (kMaxN + 1) / 2 + 1;
constexpr size_t kStageBytes = 768 * 1024;  // buffer papan lokal (stack 1 MB); pindah ke heap hanya jika penuh
constexpr long long kNoLimit = 1LL << 62;
constexpr long long kEnumBudget = 100000;  // node B&B enumerasi sebelum pindah ke DP
constexpr bool kUseDp = true;              // false = tanpa tabel DP (heap minimum, lebih lambat di papan sulit)
constexpr int kDpCap = 1 << 19;            // state DP maksimum; lebih dari ini kembali ke B&B
constexpr int kBlockBits = 12;             // tabel DP disimpan per blok 4096 state
constexpr size_t kBlock = size_t(1) << kBlockBits;

// Penampung papan: memakai buffer milik pemanggil, pindah ke heap hanya jika penuh.
struct Stage {
  uint8_t* base;
  uint8_t* out;
  uint8_t* end;
  std::vector<uint8_t> spill;

  Stage(uint8_t* buf, size_t cap) : base(buf), out(buf), end(buf + cap) {}

  void need(size_t bytes) {
    if (static_cast<size_t>(end - out) < bytes) grow(bytes);
  }
  void grow(size_t bytes) {
    const size_t used = static_cast<size_t>(out - base);
    size_t cap = 2 * static_cast<size_t>(end - base);
    while (cap < used + bytes) cap *= 2;
    std::vector<uint8_t> bigger(cap);
    std::memcpy(bigger.data(), base, used);
    spill.swap(bigger);
    base = spill.data();
    out = base + used;
    end = base + cap;
  }
};

// Tabel hash state DP: kunci = (baris, mask kolom, d1, d2), nilai g (maju) dan h (mundur). Hemat memori: kunci dan g
// dipadatkan dalam 8 byte, disimpan per blok (tanpa sisa kapasitas 2x milik vector), dan tabel hash lama dibuang dulu
// sebelum rehash.
struct DpTable {
  std::vector<std::vector<uint64_t>> rec;  // (kunci << 8) | g
  std::vector<std::vector<uint8_t>> hv;    // h
  size_t count = 0;
  std::vector<uint32_t> slot;  // indeks + 1, 0 = kosong
  uint32_t slotMask = 0;
  int shift = 0;
  bool overflow = false;

  uint64_t& recAt(size_t i) { return rec[i >> kBlockBits][i & (kBlock - 1)]; }
  uint64_t keyAt(size_t i) const { return rec[i >> kBlockBits][i & (kBlock - 1)] >> 8; }
  int gAt(size_t i) const { return static_cast<int>(rec[i >> kBlockBits][i & (kBlock - 1)] & 0xFFu); }
  int hAt(size_t i) const { return hv[i >> kBlockBits][i & (kBlock - 1)]; }
  void setH(size_t i, int v) { hv[i >> kBlockBits][i & (kBlock - 1)] = static_cast<uint8_t>(v); }

  void init() {
    slot.assign(1u << 12, 0);
    slotMask = (1u << 12) - 1u;
    shift = 64 - 12;
  }
  void initH() {
    for (size_t i = 0; i < rec.size(); ++i) hv.push_back(std::vector<uint8_t>(kBlock, uint8_t(0)));
  }
  uint32_t hashOf(uint64_t k) const { return static_cast<uint32_t>((k * 0x9E3779B97F4A7C15ull) >> shift); }
  int find(uint64_t k) const {
    for (uint32_t s = hashOf(k);; s = (s + 1) & slotMask) {
      const uint32_t v = slot[s];
      if (!v) return -1;
      if (keyAt(v - 1) == k) return static_cast<int>(v - 1);
    }
  }
  void rehash() {
    const uint32_t size = 2 * (slotMask + 1);
    std::vector<uint32_t>().swap(slot);  // buang tabel lama dulu: isinya bisa dibangun ulang dari rec
    slot.assign(size, 0);
    slotMask = size - 1;
    --shift;
    for (size_t i = 0; i < count; ++i) {
      uint32_t s = hashOf(keyAt(i));
      while (slot[s]) s = (s + 1) & slotMask;
      slot[s] = static_cast<uint32_t>(i + 1);
    }
  }
  void insertMax(uint64_t k, int gv) {
    for (uint32_t s = hashOf(k);; s = (s + 1) & slotMask) {
      const uint32_t v = slot[s];
      if (!v) {
        if (count >= static_cast<size_t>(kDpCap)) {
          overflow = true;
          return;
        }
        if ((count & (kBlock - 1)) == 0) rec.push_back(std::vector<uint64_t>(kBlock));
        recAt(count) = (k << 8) | static_cast<uint64_t>(gv);
        slot[s] = static_cast<uint32_t>(++count);
        if (4 * count > 3 * (static_cast<size_t>(slotMask) + 1)) rehash();  // load factor <= 0.75
        return;
      }
      if (keyAt(v - 1) == k) {
        uint64_t& r = recAt(v - 1);
        if (static_cast<int>(r & 0xFFu) < gv) r = (r & ~uint64_t(0xFF)) | static_cast<uint64_t>(gv);
        return;
      }
    }
  }
  void release() {
    std::vector<std::vector<uint64_t>>().swap(rec);
    std::vector<std::vector<uint8_t>>().swap(hv);
    std::vector<uint32_t>().swap(slot);
    count = 0;
  }
};

struct Walled {
  Stage& st;
  int n;
  uint32_t full;
  uint32_t freeRow[kMaxN + 2] = {};     // sel bebas per baris; freeRow[n] = 0
  int nseg[kMaxN + 2] = {};             // jumlah segmen baris
  uint32_t seg[kMaxN + 2][kMaxN] = {};  // mask setiap segmen baris
  int segBase[kMaxN + 2] = {};          // indeks global segmen pertama baris r
  int doll[kMaxSeg + 1] = {};           // doll[j] = ratu terbanyak memakai segmen j.. saja (Russian doll)
  int colBelow[kMaxN + 1] = {}, d1Below[kMaxN + 1] = {}, d2Below[kMaxN + 1] = {};  // segmen yang mulai di bawah r
  uint32_t placedRow[kMaxN + 1] = {};
  int best = 0;
  long long bbNodes = 0, bbBudget = 0;  // bbBudget < 0 = berhenti
  int bbMode = 0;                       // 0: cari maksimum (perbaikan ketat), 1: kumpulkan papan == best
  int bbCap = 0;                        // mode 0: berhenti begitu best mencapai nilai ini
  DpTable dp;
  int dpPhase = 0;  // 0 maju, 1 mundur, 2 enumerasi
  int curH = 0;
  int layerStart[kMaxN + 2] = {};

  Walled(Stage& s, int size, const std::vector<std::string>& grid) : st(s), n(size), full((1u << size) - 1u) {
    int total = 0;
    for (int r = 0; r < n; ++r) {
      uint32_t f = 0;
      for (int c = 0; c < n; ++c)
        if (grid[r][c] == '.') f |= 1u << c;
      freeRow[r] = f;
      segBase[r] = total;
      for (uint32_t rest = f; rest;) {
        const uint32_t low = rest & (0u - rest);
        const uint32_t run = rest & ~(rest + low);  // run bit 1 berurutan mulai dari `low`
        seg[r][nseg[r]++] = run;
        rest &= ~run;
      }
      total += nseg[r];
    }
    segBase[n] = segBase[n + 1] = total;
    int sc = 0, s1 = 0, s2 = 0;
    for (int r = n - 1; r >= 0; --r) {
      colBelow[r] = sc;
      d1Below[r] = s1;
      d2Below[r] = s2;
      const uint32_t f = freeRow[r], above = r ? freeRow[r - 1] : 0;
      sc += __builtin_popcount(f & ~above);
      s1 += __builtin_popcount(f & ~((above << 1) & full));
      s2 += __builtin_popcount(f & ~(above >> 1));
    }
  }

  void storeBoard(int placed) {
    st.need(static_cast<size_t>(placed));
    uint8_t* p = st.out;
    for (int r = 0; r < n; ++r)
      for (uint32_t b = placedRow[r]; b; b &= b - 1) *p++ = static_cast<uint8_t>((r << 4) | __builtin_ctz(b));
    st.out = p;
  }

  // Batas atas di awal baris r. availFrom[s] = segmen s.. pada baris ini yang masih punya sel aman.
  // M = batas dari segmen kolom / diagonal yang masih bebas (berlaku untuk seluruh sisa baris).
  int rowBound(int r, uint32_t avail, uint32_t col, uint32_t d1, uint32_t d2, int* availFrom, int& M) const {
    const uint32_t fr = freeRow[r];
    const int ns = nseg[r];
    availFrom[ns] = 0;
    for (int s = ns - 1; s >= 0; --s) availFrom[s] = availFrom[s + 1] + ((avail & seg[r][s]) != 0);
    M = __builtin_popcount(fr & ~col) + colBelow[r];
    const int m1 = __builtin_popcount(fr & ~d1) + d1Below[r];
    const int m2 = __builtin_popcount(fr & ~d2) + d2Below[r];
    if (m1 < M) M = m1;
    if (m2 < M) M = m2;
    int ub = availFrom[0] + doll[segBase[r + 1]];
    if (doll[segBase[r]] < ub) ub = doll[segBase[r]];
    return ub < M ? ub : M;
  }
  // Batas atas untuk sisa baris r mulai segmen s, dengan k ratu sudah di baris ini.
  int segBound(int r, int s, int k, const int* availFrom, int M) const {
    int ub = availFrom[s] + doll[segBase[r + 1]];
    const int d = doll[segBase[r] + s];
    if (d < ub) ub = d;
    ub += k;
    return ub < M ? ub : M;
  }

  // ---- Branch & Bound ----
  void bbSegs(int r, int s, uint32_t avail, uint32_t bits, int k, const int* availFrom, int M, uint32_t col,
              uint32_t d1, uint32_t d2, int placed) {
    if (s == nseg[r]) {
      placedRow[r] = bits;
      const uint32_t nf = freeRow[r + 1];
      bbRow(r + 1, (col | bits) & nf, ((d1 | bits) << 1) & nf, ((d2 | bits) >> 1) & nf, placed + k);
      return;
    }
    if (placed + segBound(r, s, k, availFrom, M) < best + (bbMode == 0)) return;
    uint32_t a = avail & seg[r][s];
    while (a) {
      const uint32_t b = a & (0u - a);
      a ^= b;
      bbSegs(r, s + 1, avail, bits | b, k + 1, availFrom, M, col, d1, d2, placed);
      if (bbBudget < 0) return;
    }
    bbSegs(r, s + 1, avail, bits, k, availFrom, M, col, d1, d2, placed);
  }

  void bbRow(int r, uint32_t col, uint32_t d1, uint32_t d2, int placed) {
    if (++bbNodes > bbBudget) {
      bbBudget = -1;
      return;
    }
    if (r == n) {
      if (bbMode == 0) {
        if (placed > best) {
          best = placed;
          if (best >= bbCap) bbBudget = -1;  // tidak mungkin lebih baik lagi
        }
      } else if (placed == best) {
        storeBoard(placed);
      }
      return;
    }
    const uint32_t avail = freeRow[r] & ~(col | d1 | d2);
    int availFrom[kMaxN + 1], M;
    if (placed + rowBound(r, avail, col, d1, d2, availFrom, M) < best + (bbMode == 0)) return;
    bbSegs(r, 0, avail, 0, 0, availFrom, M, col, d1, d2, placed);
  }

  // ---- DP per baris ----
  static uint64_t packKey(int r, uint32_t col, uint32_t d1, uint32_t d2) {
    return (static_cast<uint64_t>(r) << 48) | (static_cast<uint64_t>(col) << 32) | (static_cast<uint64_t>(d1) << 16) |
           d2;
  }

  void dpSegs(int r, int s, uint32_t avail, uint32_t bits, int k, const int* availFrom, int M, uint32_t col,
              uint32_t d1, uint32_t d2, int g) {
    if (dp.overflow) return;
    if (s == nseg[r]) {
      const uint32_t nf = freeRow[r + 1];
      const uint32_t nc = (col | bits) & nf, n1 = ((d1 | bits) << 1) & nf, n2 = ((d2 | bits) >> 1) & nf;
      const uint64_t key = packKey(r + 1, nc, n1, n2);
      if (dpPhase == 0) {
        dp.insertMax(key, g + k);
        return;
      }
      const int idx = dp.find(key);
      if (idx < 0) return;
      if (dpPhase == 1) {
        if (k + dp.hAt(idx) > curH) curH = k + dp.hAt(idx);
      } else if (g + k + dp.hAt(idx) == best) {
        placedRow[r] = bits;
        dpRow(r + 1, nc, n1, n2, g + k);
      }
      return;
    }
    if (g + segBound(r, s, k, availFrom, M) < best) return;
    uint32_t a = avail & seg[r][s];
    while (a) {
      const uint32_t b = a & (0u - a);
      a ^= b;
      dpSegs(r, s + 1, avail, bits | b, k + 1, availFrom, M, col, d1, d2, g);
    }
    dpSegs(r, s + 1, avail, bits, k, availFrom, M, col, d1, d2, g);
  }

  void dpRow(int r, uint32_t col, uint32_t d1, uint32_t d2, int g) {
    if (r == n) {
      storeBoard(best);
      return;
    }
    const uint32_t avail = freeRow[r] & ~(col | d1 | d2);
    int availFrom[kMaxN + 1], M;
    if (g + rowBound(r, avail, col, d1, d2, availFrom, M) < best) return;
    dpSegs(r, 0, avail, 0, 0, availFrom, M, col, d1, d2, g);
  }

  void expand(int i, int r) {
    const uint64_t k = dp.keyAt(i);
    dpRow(r, static_cast<uint32_t>(k >> 32) & 0xFFFFu, static_cast<uint32_t>(k >> 16) & 0xFFFFu,
          static_cast<uint32_t>(k) & 0xFFFFu, dp.gAt(i));
  }

  // Mengumpulkan semua papan dengan `best` ratu (best sudah eksak). false jika state melebihi kDpCap.
  bool runDp() {
    dp.init();
    dp.insertMax(packKey(0, 0, 0, 0), 0);
    dpPhase = 0;
    layerStart[0] = 0;
    for (int r = 0; r < n; ++r) {
      const int end = static_cast<int>(dp.count);
      layerStart[r + 1] = end;
      for (int i = layerStart[r]; i < end; ++i) {
        expand(i, r);
        if (dp.overflow) return false;
      }
    }
    const int fin = dp.find(packKey(n, 0, 0, 0));
    if (fin < 0) return true;
    dp.initH();
    dpPhase = 1;
    for (int r = n - 1; r >= 0; --r) {
      for (int i = layerStart[r]; i < layerStart[r + 1]; ++i) {
        curH = -1;
        expand(i, r);
        dp.setH(i, curH < 0 ? 0 : curH);
      }
    }
    dpPhase = 2;
    dpRow(0, 0, 0, 0, 0);
    return true;
  }

  void solve() {
    // Russian doll: doll[j] untuk j = total-1 .. 0. Menambah satu segmen menambah paling banyak satu ratu.
    for (int r = n - 1; r >= 0; --r) {
      for (int s = nseg[r] - 1; s >= 0; --s) {
        const int j = segBase[r] + s;
        doll[j] = doll[j + 1] + 1;  // batas atas sementara selama sub-pencarian ini
        best = doll[j + 1];
        bbMode = 0;
        bbCap = doll[j + 1] + 1;
        bbNodes = 0;
        bbBudget = kNoLimit;
        int availFrom[kMaxN + 1], M;  // sub-papan mulai di segmen s baris r, tanpa serangan dari atas
        rowBound(r, freeRow[r], 0, 0, 0, availFrom, M);
        bbSegs(r, s, freeRow[r], 0, 0, availFrom, M, 0, 0, 0, 0);
        doll[j] = best;
      }
    }
    best = doll[0];

    // Enumerasi. Tembok sedikit: B&B saja (state DP terlalu banyak). Tembok banyak: B&B dengan anggaran kecil, lalu DP.
    int walls = 0;
    for (int r = 0; r < n; ++r) walls += n - __builtin_popcount(freeRow[r]);
    bbMode = 1;
    bbNodes = 0;
    bbBudget = (!kUseDp || walls <= n + n / 4) ? kNoLimit : kEnumBudget;
    bbRow(0, 0, 0, 0, 0);
    if (bbBudget < 0) {
      st.out = st.base;
      const bool ok = runDp();
      dp.release();  // lepas tabel DP sebelum hasil dibangun
      if (!ok) {
        st.out = st.base;
        bbNodes = 0;
        bbBudget = kNoLimit;
        bbRow(0, 0, 0, 0, 0);
      }
    }
  }
};

}  // namespace

std::vector<std::vector<std::pair<int, int>>> solveWalled(int n, const std::vector<std::string>& grid) {
  if (n < 1 || n > kMaxN) return {};
  uint8_t buf[kStageBytes];
  Stage st(buf, sizeof(buf));
  int best = 0;
  {
    Walled w(st, n, grid);
    w.solve();
    best = w.best;
  }
  std::vector<std::vector<std::pair<int, int>>> res;
  if (best <= 0) return res;
  res.reserve(static_cast<size_t>(st.out - st.base) / best);
  for (const uint8_t* p = st.base; p != st.out;) {
    res.emplace_back(best);
    auto& v = res.back();
    for (int i = 0; i < best; ++i, ++p) v[i] = {*p >> 4, *p & 15};
  }
  return res;
}
