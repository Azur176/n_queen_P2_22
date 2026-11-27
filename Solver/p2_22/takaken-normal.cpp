// Solver NORMAL - Kelompok P2_22 (Paralel 2, Analisis Algoritme IPB University)
//
// Algoritme: Takaken = backtracking bitmask (kolom, diagonal kiri, diagonal kanan sebagai register geser) yang hanya
// menelusuri representatif kanonik di bawah 8 simetri papan (rotasi 90/180/270 + cermin). Ratu baris 0 di pojok
// atau di tepi dibatasi (BOUND1/BOUND2, SIDEMASK, LASTMASK) sehingga tiap kelas simetri ditemukan tepat sekali, lalu
// setiap representatif dikembangkan menjadi orbitnya (8, 4 atau 2 papan berbeda). Pohon pencarian ~1/8 backtracking
// biasa; dua baris terakhir ditangani langsung tanpa rekursi, dan pencarian tepi memakai stack eksplisit.
//
// Tanpa variabel global: semua state ada di struct yang dibuat di dalam solveNQueens(). Solusi ditampung dulu di buffer
// lokal 1 byte per sel, lalu hasil akhir dibuat dengan reserve() yang pas.
#include <cstdint>
#include <cstring>
#include <vector>

#include "nqueens.h"

namespace {

constexpr size_t kStageBytes = 180 * 1024;  // buffer lokal; cukup untuk semua solusi N <= 12

// Penampung solusi: memakai buffer milik pemanggil, pindah ke heap hanya jika penuh.
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
  std::vector<std::vector<int>> rows(int n) const {
    std::vector<std::vector<int>> res;
    res.reserve(static_cast<size_t>(out - base) / n);
    for (const uint8_t* p = base; p != out; p += n) res.emplace_back(p, p + n);
    return res;
  }
};

struct Takaken {
  Stage& st;
  int n, last, bound1, bound2;
  uint32_t mask, topbit, sidemask, lastmask, endbit;
  uint32_t B[32];  // B[y] = bit kolom ratu pada baris y

  Takaken(Stage& s, int size) : st(s), n(size), last(size - 1), bound1(0), bound2(0) {
    mask = (1u << n) - 1u;
    topbit = 1u << last;
    sidemask = lastmask = endbit = 0;
  }

  // Menulis semua bayangan berbeda dari papan B di bawah 8 simetri. orbit = 8, 4 atau 2.
  void emitOrbit(int orbit) {
    const int m = last;
    st.need(8 * static_cast<size_t>(n));
    uint8_t q[32], inv[32];
    for (int r = 0; r < n; ++r) {
      q[r] = static_cast<uint8_t>(__builtin_ctz(B[r]));
      inv[q[r]] = static_cast<uint8_t>(r);
    }
    uint8_t* p = st.out;
    if (orbit == 8) {
      for (int r = 0; r < n; ++r) {
        const uint8_t a = q[r], b = q[m - r], c = inv[r], d = inv[m - r];
        p[r] = a;
        p[n + r] = static_cast<uint8_t>(m - a);
        p[2 * n + r] = b;
        p[3 * n + r] = static_cast<uint8_t>(m - b);
        p[4 * n + r] = c;
        p[5 * n + r] = static_cast<uint8_t>(m - c);
        p[6 * n + r] = d;
        p[7 * n + r] = static_cast<uint8_t>(m - d);
      }
      st.out = p + 8 * n;
      return;
    }
    uint8_t img[8][32];
    for (int r = 0; r < n; ++r) {
      const uint8_t a = q[r], b = q[m - r], c = inv[r], d = inv[m - r];
      img[0][r] = a;
      img[1][r] = static_cast<uint8_t>(m - a);
      img[2][r] = b;
      img[3][r] = static_cast<uint8_t>(m - b);
      img[4][r] = c;
      img[5][r] = static_cast<uint8_t>(m - c);
      img[6][r] = d;
      img[7][r] = static_cast<uint8_t>(m - d);
    }
    for (int i = 0; i < 8; ++i) {  // papan simetris: buang bayangan yang kembar
      bool dup = false;
      for (int j = 0; j < i && !dup; ++j) dup = std::memcmp(img[i], img[j], n) == 0;
      if (dup) continue;
      std::memcpy(p, img[i], n);
      p += n;
    }
    st.out = p;
  }

  // Uji simetri Takaken: 0 jika B bukan representatif kanonik, selain itu ukuran orbitnya.
  int check() const {
    const int E = last;
    int own, you;
    uint32_t bit, ptn;
    if (B[bound2] == 1) {  // rotasi 90 derajat
      for (ptn = 2, own = 1; own <= E; ++own, ptn <<= 1) {
        bit = 1;
        for (you = E; B[you] != ptn && B[own] >= bit; --you) bit <<= 1;
        if (B[own] > bit) return 0;
        if (B[own] < bit) break;
      }
      if (own > E) return 2;
    }
    if (B[E] == endbit) {  // rotasi 180 derajat
      for (you = E - 1, own = 1; own <= E; ++own, --you) {
        bit = 1;
        for (ptn = topbit; ptn != B[you] && B[own] >= bit; ptn >>= 1) bit <<= 1;
        if (B[own] > bit) return 0;
        if (B[own] < bit) break;
      }
      if (own > E) return 4;
    }
    if (B[bound1] == topbit) {  // rotasi 270 derajat
      for (ptn = topbit >> 1, own = 1; own <= E; ++own, ptn >>= 1) {
        bit = 1;
        for (you = 0; B[you] != ptn && B[own] >= bit; ++you) bit <<= 1;
        if (B[own] > bit) return 0;
        if (B[own] < bit) break;
      }
    }
    return 8;
  }

  // Ratu di pojok (0,0): setiap kelas seperti ini punya 8 papan berbeda.
  void corner(int y, uint32_t left, uint32_t down, uint32_t right) {
    uint32_t bm = mask & ~(left | down | right);
    if (y < bound1) bm &= ~2u;
    if (y == last - 1) {  // dua baris terakhir langsung
      while (bm) {
        const uint32_t bit = bm & (0u - bm);
        bm ^= bit;
        const uint32_t fin = mask & ~(((left | bit) << 1) | down | bit | ((right | bit) >> 1));
        if (fin) {
          B[y] = bit;
          B[y + 1] = fin;
          emitOrbit(8);
        }
      }
      return;
    }
    while (bm) {
      const uint32_t bit = bm & (0u - bm);
      bm ^= bit;
      B[y] = bit;
      corner(y + 1, (left | bit) << 1, down | bit, (right | bit) >> 1);
    }
  }

  // Ratu baris 0 bukan di pojok: pencarian iteratif dengan stack eksplisit, dua baris terakhir langsung.
  void edge() {
    uint32_t bms[32], ls[32], ds[32], rs[32];
    const uint32_t mk = mask, side = sidemask, lastm = lastmask;
    const int last1 = last - 1, b1 = bound1, b2 = bound2;
    int y = 1;
    {
      const uint32_t bit = B[0];
      ls[1] = bit << 1;
      ds[1] = bit;
      rs[1] = bit >> 1;
      uint32_t bm = mk & ~(ls[1] | ds[1] | rs[1]);
      if (1 < b1) bm &= ~side;
      bms[1] = bm;
    }
    for (;;) {
      const uint32_t bm = bms[y];
      if (!bm) {
        if (--y == 0) return;
        continue;
      }
      const uint32_t bit = bm & (0u - bm);
      bms[y] = bm ^ bit;
      B[y] = bit;
      const uint32_t l = (ls[y] | bit) << 1, d = ds[y] | bit, r = (rs[y] | bit) >> 1;
      if (y == last1) {
        const uint32_t fin = mk & ~(l | d | r);
        if (fin && !(fin & lastm)) {
          B[y + 1] = fin;
          const int k = check();
          if (k) emitOrbit(k);
        }
        continue;
      }
      ++y;
      uint32_t nb = mk & ~(l | d | r);
      if (y < b1) {
        nb &= ~side;
      } else if (y == b2) {
        if (!(d & side)) nb = 0;
        else if ((d & side) != side) nb &= side;
      }
      ls[y] = l;
      ds[y] = d;
      rs[y] = r;
      bms[y] = nb;
    }
  }

  void run() {  // butuh N >= 4
    B[0] = 1;
    for (bound1 = 2; bound1 < last; ++bound1) {
      const uint32_t bit = 1u << bound1;
      B[1] = bit;
      corner(2, (2u | bit) << 1, 1u | bit, bit >> 1);
    }
    sidemask = lastmask = topbit | 1u;
    endbit = topbit >> 1;
    for (bound1 = 1, bound2 = n - 2; bound1 < bound2; ++bound1, --bound2) {
      B[0] = 1u << bound1;
      edge();
      lastmask |= (lastmask >> 1) | (lastmask << 1);
      endbit >>= 1;
    }
  }
};

}  // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  if (n < 1 || n > 16) return {};
  if (n < 4) return n == 1 ? std::vector<std::vector<int>>{{0}} : std::vector<std::vector<int>>{};
  uint8_t buf[kStageBytes];
  Stage st(buf, sizeof(buf));
  Takaken tk(st, n);
  tk.run();
  return st.rows(n);
}
