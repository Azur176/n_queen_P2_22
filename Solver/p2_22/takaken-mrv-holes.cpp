#include "nqueens.h"
#include <cstdint>
#include <string>
#include <vector>

namespace {

void backtrack(int row, int n, uint32_t colsMask, uint32_t diag1Mask, uint32_t diag2Mask,
               const std::vector<uint32_t>& validRowMask, std::vector<int>& current,
               std::vector<std::vector<int>>& solutions) {
  if (row == n) {
    solutions.push_back(current);
    NQ_SNAPSHOT(nq::queensOf(current), "solution " + std::to_string(solutions.size()));
    return;
  }

  uint32_t available = validRowMask[row] & ~(colsMask | diag1Mask | diag2Mask);
  while (available) {
    uint32_t bit = available & -available;
    available ^= bit;

    int col = __builtin_ctz(bit);
    current[row] = col;

    backtrack(row + 1, n, colsMask | bit, (diag1Mask | bit) << 1, (diag2Mask | bit) >> 1,
              validRowMask, current, solutions);
  }
}

}  // namespace

std::vector<std::vector<int>> solveHoles(int n, const std::vector<std::string>& grid) {
  std::vector<std::vector<int>> solutions;
  if (n <= 0 || n > 32 || static_cast<int>(grid.size()) != n) return solutions;

  std::vector<uint32_t> validRowMask(n, 0u);
  for (int r = 0; r < n; ++r) {
    if (static_cast<int>(grid[r].size()) != n) return solutions;
    uint32_t mask = 0u;
    for (int c = 0; c < n; ++c) {
      if (grid[r][c] == '.') {
        mask |= (1u << c);
      }
    }
    if (mask == 0u) return solutions;  // Seluruh baris tertutup lubang, mustahil ada solusi
    validRowMask[r] = mask;
  }

  if (n >= 10) solutions.reserve(10000);

  std::vector<int> current(n, 0);
  backtrack(0, n, 0u, 0u, 0u, validRowMask, current, solutions);
  return solutions;
}