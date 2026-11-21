#include "nqueens.h"
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

namespace {

void backtrack(int row, int n, uint32_t colsMask, uint32_t diag1Mask, uint32_t diag2Mask,
               uint32_t allOnes, const std::vector<int>& fixedCol, std::vector<int>& current,
               std::vector<std::vector<int>>& solutions) {
  if (row == n) {
    solutions.push_back(current);
    NQ_SNAPSHOT(nq::queensOf(current), "solution " + std::to_string(solutions.size()));
    return;
  }

  // Jika baris ini sudah memiliki ratu pre-placed, langsung lanjut ke baris berikutnya
  if (fixedCol[row] != -1) {
    backtrack(row + 1, n, colsMask, diag1Mask << 1, diag2Mask >> 1, allOnes, fixedCol, current,
              solutions);
    return;
  }

  uint32_t available = allOnes & ~(colsMask | diag1Mask | diag2Mask);
  while (available) {
    uint32_t bit = available & -available;
    available ^= bit;

    int col = __builtin_ctz(bit);
    current[row] = col;

    backtrack(row + 1, n, colsMask | bit, (diag1Mask | bit) << 1, (diag2Mask | bit) >> 1,
              allOnes, fixedCol, current, solutions);
  }
}

}  // namespace

std::vector<std::vector<int>> solvePreplaced(int n,
                                             const std::vector<std::pair<int, int>>& preplaced) {
  std::vector<std::vector<int>> solutions;
  if (n <= 0 || n > 31) return solutions;

  std::vector<int> fixedCol(n, -1);
  uint32_t colsMask = 0u;
  uint32_t diag1Mask = 0u;  // diagonal (row - col), digeser relatif terhadap row = 0
  uint32_t diag2Mask = 0u;  // diagonal (row + col), digeser relatif terhadap row = 0

  for (const auto& q : preplaced) {
    int r = q.first;
    int c = q.second;
    if (r < 0 || r >= n || c < 0 || c >= n) return solutions;

    // Jika ada 2 ratu pre-placed di baris yang sama
    if (fixedCol[r] != -1) return solutions;

    uint32_t bit = 1u << c;
    // Posisi proyeksi diagonal ratu (r, c) saat backtracking dimulai di row = 0
    uint32_t d1 = bit << r;
    uint32_t d2 = (r >= 0) ? (bit >> r) : 0u;

    // Cek konflik kolom atau diagonal antar-ratu pre-placed
    if (colsMask & bit) return solutions;
    if (diag1Mask & d1) return solutions;
    // Untuk diag2 (r + c tetap), cek apakah r + c sudah terpakai lewat mask (1u << (r + c))
    fixedCol[r] = c;
    colsMask |= bit;
    diag1Mask |= d1;
  }

  // Rekonstruksi diag2Mask (r + c) secara presisi pada row = 0
  // Pada baris r, bit yang terlarang akibat ratu di (rp, cp) dengan rp + cp == r + c adalah (1u << (rp + cp - r))
  uint32_t sumDiagMask = 0u;
  for (const auto& q : preplaced) {
    int s = q.first + q.second;
    uint32_t sBit = 1u << s;
    if (sumDiagMask & sBit) return solutions;  // konflik diagonal r + c antar-ratu pre-placed
    sumDiagMask |= sBit;
  }
  diag2Mask = sumDiagMask;

  if (n >= 10 && preplaced.empty()) solutions.reserve(15000);

  std::vector<int> current = fixedCol;
  uint32_t allOnes = (1u << n) - 1u;

  backtrack(0, n, colsMask, diag1Mask, diag2Mask, allOnes, fixedCol, current, solutions);
  return solutions;
}