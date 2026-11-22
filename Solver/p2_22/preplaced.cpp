#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "nqueens.h"

namespace {

inline int ctz32(uint32_t x) {
  return __builtin_ctz(x);
}

void backtrack(int r, int n, uint32_t fullMask, uint32_t colMask, uint32_t d1Mask, uint32_t d2Mask,
               const std::vector<int>& fixedCol, std::vector<int>& cols,
               std::vector<std::vector<int>>& solutions) {
  if (r == n) {
    solutions.push_back(cols);
    NQ_SNAPSHOT(nq::queensOf(cols), "solution " + std::to_string(solutions.size()));
    return;
  }

  if (fixedCol[r] >= 0) {
    backtrack(r + 1, n, fullMask, colMask, d1Mask, d2Mask, fixedCol, cols, solutions);
    return;
  }

  uint32_t blocked = colMask | (d1Mask >> r) | (d2Mask >> (n - 1 - r));
  uint32_t avail = fullMask & ~blocked;

  while (avail != 0) {
    uint32_t bit = avail & (~avail + 1u);
    avail ^= bit;
    int c = ctz32(bit);

    cols[r] = c;
    backtrack(r + 1, n, fullMask, colMask | bit, d1Mask | (1u << (r + c)),
              d2Mask | (1u << (c - r + n - 1)), fixedCol, cols, solutions);
    cols[r] = -1;
  }
}

}

std::vector<std::vector<int>> solvePreplaced(int n, const std::vector<std::pair<int, int>>& preplaced) {
  std::vector<std::vector<int>> solutions;
  std::vector<int> fixedCol(n, -1);
  uint32_t colMask = 0, d1Mask = 0, d2Mask = 0;

  for (const auto& q : preplaced) {
    int r = q.first, c = q.second;
    if (r < 0 || r >= n || c < 0 || c >= n) return solutions;
    if (fixedCol[r] >= 0) return solutions;
    uint32_t cBit = 1u << c;
    uint32_t d1Bit = 1u << (r + c);
    uint32_t d2Bit = 1u << (c - r + n - 1);
    if ((colMask & cBit) || (d1Mask & d1Bit) || (d2Mask & d2Bit)) return solutions;
    fixedCol[r] = c;
    colMask |= cBit;
    d1Mask |= d1Bit;
    d2Mask |= d2Bit;
  }

  std::vector<int> cols = fixedCol;
  uint32_t fullMask = (n >= 32) ? ~0u : ((1u << n) - 1u);
  backtrack(0, n, fullMask, colMask, d1Mask, d2Mask, fixedCol, cols, solutions);
  return solutions;
}