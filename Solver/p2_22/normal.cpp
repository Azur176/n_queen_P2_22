#include "nqueens.h"
#include <cstdint>
#include <vector>

namespace {

void backtrack(int row, int n, uint32_t colsMask, uint32_t diag1Mask, uint32_t diag2Mask,
               uint32_t allOnes, std::vector<int>& current,
               std::vector<std::vector<int>>& solutions) {
  if (row == n) {
    solutions.push_back(current);
    NQ_SNAPSHOT(nq::queensOf(current), "solution " + std::to_string(solutions.size()));
    return;
  }

  uint32_t available = allOnes & ~(colsMask | diag1Mask | diag2Mask);
  while (available) {
    uint32_t bit = available & -available;
    available ^= bit;

    int col = __builtin_ctz(bit);
    current[row] = col;

    backtrack(row + 1, n, colsMask | bit, (diag1Mask | bit) << 1, (diag2Mask | bit) >> 1,
              allOnes, current, solutions);
  }
}

}  // namespace

std::vector<std::vector<int>> solveNQueens(int n) {
  std::vector<std::vector<int>> solutions;
  if (n <= 0 || n > 31) return solutions;

  // Pre-allocate kapasitas perkiraan untuk menghindari realokasi memori berulang
  if (n >= 10) solutions.reserve(15000);

  std::vector<int> current(n, 0);
  uint32_t allOnes = (1u << n) - 1u;

  backtrack(0, n, 0u, 0u, 0u, allOnes, current, solutions);
  return solutions;
}