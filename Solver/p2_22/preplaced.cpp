#include "nqueens.h"
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

namespace {

void backtrack(int row, int n, uint32_t colsMask, uint64_t d1Mask, uint64_t d2Mask,
               uint32_t allOnes, const std::vector<int>& fixedCol, std::vector<int>& current,
               std::vector<std::vector<int>>& solutions) {
  if (row == n) {
    solutions.push_back(current);
    NQ_SNAPSHOT(nq::queensOf(current), "solution " + std::to_string(solutions.size()));
    return;
  }

  if (fixedCol[row] != -1) {
    backtrack(row + 1, n, colsMask, d1Mask, d2Mask, allOnes, fixedCol, current, solutions);
    return;
  }

  uint32_t blockedDiag1 = static_cast<uint32_t>(d1Mask >> (n - 1 - row));
  uint32_t blockedDiag2 = static_cast<uint32_t>(d2Mask >> row);
  uint32_t available = allOnes & ~(colsMask | blockedDiag1 | blockedDiag2);

  while (available) {
    uint32_t bit = available & -available;
    available ^= bit;

    int col = __builtin_ctz(bit);
    current[row] = col;

    uint64_t d1Bit = 1ULL << ((n - 1 - row) + col);
    uint64_t d2Bit = 1ULL << (row + col);

    backtrack(row + 1, n, colsMask | bit, d1Mask | d1Bit, d2Mask | d2Bit, allOnes, fixedCol,
              current, solutions);
  }
}

}  // namespace

std::vector<std::vector<int>> solvePreplaced(int n,
                                             const std::vector<std::pair<int, int>>& preplaced) {
  std::vector<std::vector<int>> solutions;
  if (n <= 0 || n > 32) return solutions;

  std::vector<int> fixedCol(n, -1);
  uint32_t colsMask = 0u;
  uint64_t d1Mask = 0ULL;  // bit ke-((n - 1 - r) + c)
  uint64_t d2Mask = 0ULL;  // bit ke-(r + c)

  for (const auto& q : preplaced) {
    int r = q.first;
    int c = q.second;
    if (r < 0 || r >= n || c < 0 || c >= n) return solutions;
    if (fixedCol[r] != -1) return solutions;

    uint32_t colBit = 1u << c;
    uint64_t d1Bit = 1ULL << ((n - 1 - r) + c);
    uint64_t d2Bit = 1ULL << (r + c);

    if ((colsMask & colBit) || (d1Mask & d1Bit) || (d2Mask & d2Bit)) {
      return solutions;
    }

    fixedCol[r] = c;
    colsMask |= colBit;
    d1Mask |= d1Bit;
    d2Mask |= d2Bit;
  }

  if (n >= 10 && preplaced.empty()) solutions.reserve(15000);

  std::vector<int> current = fixedCol;
  uint32_t allOnes = (n == 32) ? 0xFFFFFFFFu : ((1u << n) - 1u);

  backtrack(0, n, colsMask, d1Mask, d2Mask, allOnes, fixedCol, current, solutions);
  return solutions;
}