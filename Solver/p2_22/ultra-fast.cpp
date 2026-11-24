// Solver Kompetisi Kelompok P2_22: Ultra-Fast Bitmask + Symmetry + MRV + Segment BnB
// Kelompok 22 (Paralel 2) - Afdha Auliya Atiq (M0403241163)
//
// Optimasi Kecepatan & Memori:
// 1. Normal: Vertical Mirror Symmetry (hanya telusuri separuh pohon pencarian),
//    shift-register bitmask (col, ld, rd) murni di register CPU, serta inlining baris terakhir
//    (menghilangkan ~50% pemanggilan fungsi rekursif) + pre-reserve OEIS A000170.
// 2. Pre-placed: Jika P == 0 langsung memakai jalur Normal simetri; jika P > 0 memakai
//    MRV (Minimum Remaining Values) fail-first + inlining baris terakhir.
// 3. Holes: MRV fail-first + inlining baris terakhir.
// 4. Walled: Dekomposisi segmen + sorting segmen terpendek + Greedy Warm-Start +
//    128-bit bitset segmen (O(1) bitwise check) + Upper Bound min(remH, freeV, freeD1, freeD2).

#include <algorithm>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "nqueens.h"

namespace {

inline int ctz32(uint32_t x) { return __builtin_ctz(x); }
inline int popcnt32(uint32_t x) { return __builtin_popcount(x); }

// ---- 1. NORMAL (Symmetry Breaking + Shift-Register Bitmask + Last-Row Inlining) ----
struct NormalFast {
  int n;
  uint32_t fullMask;
  int cols[16];
  std::vector<std::vector<int>> solutions;

  void emitPair() {
    solutions.emplace_back(cols, cols + n);
    NQ_SNAPSHOT(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
    std::vector<int> mirror(n);
    for (int i = 0; i < n; ++i) mirror[i] = n - 1 - cols[i];
    solutions.push_back(std::move(mirror));
    NQ_SNAPSHOT(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
  }

  void emitSingle() {
    solutions.emplace_back(cols, cols + n);
    NQ_SNAPSHOT(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
  }

  template <bool kMirror>
  void dfs(int r, uint32_t col, uint32_t ld, uint32_t rd) {
    uint32_t avail = fullMask & ~(col | ld | rd);
    if (r == n - 2) {
      // Inline baris n-2 dan n-1 tanpa rekursi tambahan
      while (avail != 0) {
        uint32_t bit = avail & (~avail + 1u);
        avail ^= bit;
        uint32_t nCol = col | bit;
        uint32_t lastAvail = fullMask & ~(nCol | ((ld | bit) << 1) | ((rd | bit) >> 1));
        if (lastAvail != 0) {
          cols[r] = ctz32(bit);
          cols[r + 1] = ctz32(lastAvail);
          if constexpr (kMirror)
            emitPair();
          else
            emitSingle();
        }
      }
      return;
    }

    while (avail != 0) {
      uint32_t bit = avail & (~avail + 1u);
      avail ^= bit;
      cols[r] = ctz32(bit);
      dfs<kMirror>(r + 1, col | bit, ((ld | bit) << 1) & fullMask, (rd | bit) >> 1);
    }
  }

  std::vector<std::vector<int>> run(int boardN) {
    n = boardN;
    fullMask = (1u << n) - 1u;
    static const size_t kOeis[] = {0, 1, 0, 0, 2, 10, 4, 40, 92, 352, 724, 2680, 14200};
    if (n >= 0 && n <= 12) solutions.reserve(kOeis[n]);

    const int half = n / 2;
    // Separuh kiri baris 0 -> otomatis dicerminkan ke separuh kanan
    for (int c = 0; c < half; ++c) {
      cols[0] = c;
      uint32_t bit = 1u << c;
      dfs<true>(1, bit, (bit << 1) & fullMask, bit >> 1);
    }

    // Jika N ganjil, kolom tengah pada baris 0 dicerminkan terhadap baris 1
    if (n & 1) {
      int mid = half;
      cols[0] = mid;
      uint32_t bit0 = 1u << mid;
      uint32_t col1 = bit0;
      uint32_t ld1 = (bit0 << 1) & fullMask;
      uint32_t rd1 = bit0 >> 1;
      // Pada baris 1, kolom < mid dicerminkan ke kolom > mid (kolom mid tidak mungkin aman)
      uint32_t leftMask = (1u << mid) - 1u;
      uint32_t avail1 = leftMask & ~(col1 | ld1 | rd1);
      while (avail1 != 0) {
        uint32_t bit1 = avail1 & (~avail1 + 1u);
        avail1 ^= bit1;
        cols[1] = ctz32(bit1);
        if (n == 3) {
          // n >= 4 di tester, tetap aman untuk n kecil
        }
        dfs<true>(2, col1 | bit1, ((ld1 | bit1) << 1) & fullMask, (rd1 | bit1) >> 1);
      }
    }
    return std::move(solutions);
  }
};

// ---- 2. MRV + LAST-ROW INLINING (Pre-placed & Holes) ----
struct MrvFast {
  int n;
  uint32_t fullMask;
  uint32_t allowed[16];
  int cols[16];
  std::vector<std::vector<int>> solutions;

  void search(uint32_t remRows, uint32_t colMask, uint32_t d1Mask, uint32_t d2Mask) {
    // Jika tinggal 1 baris tersisa, langsung cek O(1) tanpa loop MRV
    if ((remRows & (remRows - 1u)) == 0u) {
      int r = ctz32(remRows);
      uint32_t avail = allowed[r] & ~(colMask | (d1Mask >> r) | (d2Mask >> (n - 1 - r)));
      while (avail != 0) {
        uint32_t bit = avail & (~avail + 1u);
        avail ^= bit;
        cols[r] = ctz32(bit);
        solutions.emplace_back(cols, cols + n);
        NQ_SNAPSHOT(nq::queensOf(solutions.back()), "solution " + std::to_string(solutions.size()));
      }
      return;
    }

    int bestRow = -1;
    int minChoices = n + 1;
    uint32_t bestAvail = 0;

    uint32_t tmp = remRows;
    while (tmp != 0) {
      uint32_t rBit = tmp & (~tmp + 1u);
      tmp ^= rBit;
      int r = ctz32(rBit);
      uint32_t avail = allowed[r] & ~(colMask | (d1Mask >> r) | (d2Mask >> (n - 1 - r)));
      int cnt = popcnt32(avail);
      if (cnt == 0) return;
      if (cnt < minChoices) {
        minChoices = cnt;
        bestRow = r;
        bestAvail = avail;
        if (cnt == 1) break;
      }
    }

    uint32_t nextRem = remRows ^ (1u << bestRow);
    while (bestAvail != 0) {
      uint32_t cBit = bestAvail & (~bestAvail + 1u);
      bestAvail ^= cBit;
      int c = ctz32(cBit);
      cols[bestRow] = c;
      search(nextRem, colMask | cBit, d1Mask | (1u << (bestRow + c)),
             d2Mask | (1u << (c - bestRow + n - 1)));
    }
  }
};

// ---- 3. WALLED (128-bit Segment Bitset + Greedy Warm-Start + Sorted BnB) ----
struct Bitset128 {
  uint64_t lo = 0, hi = 0;
  inline bool test(int idx) const {
    return (idx < 64) ? ((lo >> idx) & 1ULL) : ((hi >> (idx - 64)) & 1ULL);
  }
  inline void set(int idx) {
    if (idx < 64)
      lo |= (1ULL << idx);
    else
      hi |= (1ULL << (idx - 64));
  }
  inline void clear(int idx) {
    if (idx < 64)
      lo &= ~(1ULL << idx);
    else
      hi &= ~(1ULL << (idx - 64));
  }
};

class WalledFast {
 public:
  WalledFast(int n, const std::vector<std::string>& grid) : n_(n), grid_(grid) {}

  std::vector<std::vector<std::pair<int, int>>> run() {
    buildAndSort();
    greedyWarmStart();
    dfs(0);
    return std::move(bestBoards_);
  }

 private:
  struct Cell {
    int r, c, vId, d1Id, d2Id;
  };

  int n_;
  const std::vector<std::string>& grid_;
  std::vector<std::vector<Cell>> hSegs_;
  Bitset128 usedV_, usedD1_, usedD2_;
  int freeV_ = 0, freeD1_ = 0, freeD2_ = 0;
  std::vector<std::pair<int, int>> current_;
  std::vector<std::vector<std::pair<int, int>>> bestBoards_;
  size_t bestSize_ = 0;

  void buildAndSort() {
    int vId[12][12], d1Id[12][12], d2Id[12][12];
    int vCnt = 0;
    for (int c = 0; c < n_; ++c) {
      bool ins = false;
      for (int r = 0; r < n_; ++r) {
        if (grid_[r][c] == '.') {
          if (!ins) {
            ins = true;
            ++vCnt;
          }
          vId[r][c] = vCnt - 1;
        } else {
          ins = false;
        }
      }
    }

    int d1Cnt = 0;
    for (int diff = -(n_ - 1); diff <= n_ - 1; ++diff) {
      bool ins = false;
      for (int r = 0; r < n_; ++r) {
        int c = r - diff;
        if (c < 0 || c >= n_) continue;
        if (grid_[r][c] == '.') {
          if (!ins) {
            ins = true;
            ++d1Cnt;
          }
          d1Id[r][c] = d1Cnt - 1;
        } else {
          ins = false;
        }
      }
    }

    int d2Cnt = 0;
    for (int sum = 0; sum <= 2 * (n_ - 1); ++sum) {
      bool ins = false;
      for (int r = 0; r < n_; ++r) {
        int c = sum - r;
        if (c < 0 || c >= n_) continue;
        if (grid_[r][c] == '.') {
          if (!ins) {
            ins = true;
            ++d2Cnt;
          }
          d2Id[r][c] = d2Cnt - 1;
        } else {
          ins = false;
        }
      }
    }

    freeV_ = vCnt;
    freeD1_ = d1Cnt;
    freeD2_ = d2Cnt;

    for (int r = 0; r < n_; ++r) {
      std::vector<Cell> seg;
      for (int c = 0; c < n_; ++c) {
        if (grid_[r][c] == '.') {
          seg.push_back({r, c, vId[r][c], d1Id[r][c], d2Id[r][c]});
        } else if (!seg.empty()) {
          hSegs_.push_back(std::move(seg));
          seg.clear();
        }
      }
      if (!seg.empty()) hSegs_.push_back(std::move(seg));
    }

    std::sort(hSegs_.begin(), hSegs_.end(),
              [](const std::vector<Cell>& a, const std::vector<Cell>& b) { return a.size() < b.size(); });
  }

  void greedyWarmStart() {
    Bitset128 gV, gD1, gD2;
    size_t cnt = 0;
    for (const auto& seg : hSegs_) {
      for (const Cell& cell : seg) {
        if (!gV.test(cell.vId) && !gD1.test(cell.d1Id) && !gD2.test(cell.d2Id)) {
          gV.set(cell.vId);
          gD1.set(cell.d1Id);
          gD2.set(cell.d2Id);
          ++cnt;
          break;
        }
      }
    }
    bestSize_ = cnt;
  }

  inline size_t upperBound(size_t hIdx) const {
    size_t cap = hSegs_.size() - hIdx;
    if (static_cast<size_t>(freeV_) < cap) cap = static_cast<size_t>(freeV_);
    if (static_cast<size_t>(freeD1_) < cap) cap = static_cast<size_t>(freeD1_);
    if (static_cast<size_t>(freeD2_) < cap) cap = static_cast<size_t>(freeD2_);
    return current_.size() + cap;
  }

  void dfs(size_t hIdx) {
    if (upperBound(hIdx) < bestSize_) return;

    if (hIdx == hSegs_.size()) {
      if (current_.size() > bestSize_) {
        bestSize_ = current_.size();
        bestBoards_.clear();
        bestBoards_.push_back(current_);
        NQ_SNAPSHOT(current_, "new record: " + std::to_string(bestSize_) + " queens");
      } else if (current_.size() == bestSize_) {
        bestBoards_.push_back(current_);
        NQ_SNAPSHOT(current_, "optimal board #" + std::to_string(bestBoards_.size()));
      }
      return;
    }

    for (const Cell& cell : hSegs_[hIdx]) {
      if (!usedV_.test(cell.vId) && !usedD1_.test(cell.d1Id) && !usedD2_.test(cell.d2Id)) {
        usedV_.set(cell.vId);
        usedD1_.set(cell.d1Id);
        usedD2_.set(cell.d2Id);
        --freeV_;
        --freeD1_;
        --freeD2_;
        current_.emplace_back(cell.r, cell.c);

        dfs(hIdx + 1);

        current_.pop_back();
        ++freeV_;
        ++freeD1_;
        ++freeD2_;
        usedV_.clear(cell.vId);
        usedD1_.clear(cell.d1Id);
        usedD2_.clear(cell.d2Id);
      }
    }

    if (upperBound(hIdx + 1) >= bestSize_) {
      dfs(hIdx + 1);
    }
  }
};

}  // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  return NormalFast().run(n);
}

std::vector<std::vector<int>> solvePreplaced(int n, const std::vector<std::pair<int, int>>& preplaced) {
  if (preplaced.empty()) return NormalFast().run(n);

  MrvFast solver;
  solver.n = n;
  solver.fullMask = (1u << n) - 1u;
  for (int r = 0; r < n; ++r) {
    solver.allowed[r] = solver.fullMask;
    solver.cols[r] = -1;
  }

  uint32_t colMask = 0, d1Mask = 0, d2Mask = 0;
  uint32_t remRows = solver.fullMask;
  for (const auto& q : preplaced) {
    int r = q.first, c = q.second;
    if (r < 0 || r >= n || c < 0 || c >= n) return {};
    if (solver.cols[r] >= 0) return {};
    uint32_t cBit = 1u << c;
    uint32_t d1Bit = 1u << (r + c);
    uint32_t d2Bit = 1u << (c - r + n - 1);
    if ((colMask & cBit) || (d1Mask & d1Bit) || (d2Mask & d2Bit)) return {};
    solver.cols[r] = c;
    remRows ^= (1u << r);
    colMask |= cBit;
    d1Mask |= d1Bit;
    d2Mask |= d2Bit;
  }

  if (remRows == 0) {
    solver.solutions.emplace_back(solver.cols, solver.cols + n);
    return std::move(solver.solutions);
  }
  solver.search(remRows, colMask, d1Mask, d2Mask);
  return std::move(solver.solutions);
}

std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  MrvFast solver;
  solver.n = n;
  solver.fullMask = (1u << n) - 1u;
  for (int r = 0; r < n; ++r) {
    uint32_t mask = 0;
    for (int c = 0; c < n; ++c) {
      if (grid[r][c] != 'H') mask |= (1u << c);
    }
    if (mask == 0) return {};
    solver.allowed[r] = mask;
    solver.cols[r] = -1;
  }
  solver.search(solver.fullMask, 0u, 0u, 0u);
  return std::move(solver.solutions);
}

std::vector<std::vector<std::pair<int, int>>> solveWalled(int n, const std::vector<std::string>& grid) {
  return WalledFast(n, grid).run();
}
