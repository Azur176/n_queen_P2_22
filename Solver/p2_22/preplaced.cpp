#include "nqueens.h"
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

namespace {

void backtrack(int row, int n, uint32_t colsMask, uint32_t d1Mask, uint32_t d2Mask,
               uint32_t allOnes, const std::vector<int>& fixedCol, std::vector<int>& current,
               std::vector<std::vector<int>>& solutions) {
  if (row == n) {
    solutions.push_back(current);
    NQ_SNAPSHOT(nq::queensOf(current), "solution " + std::to_string(solutions.size()));
    return;
  }

  // Baris ini sudah dikunci oleh ratu pre-placed
  if (fixedCol[row] != -1) {
    backtrack(row + 1, n, colsMask, d1Mask, d2Mask, allOnes, fixedCol, current, solutions);
    return;
  }

  // Proyeksi diagonal 1: indeks (n - 1 - row) + col
  // Proyeksi diagonal 2: indeks row + col
  uint32_t blockedDiag1 = d1Mask >> (n - 1 - row);
  uint32_t blockedDiag2 = d2Mask >> row;
  uint32_t available = allOnes & ~(colsMask | blockedDiag1 | blockedDiag2);

  while (available) {
    uint32_t bit = available & -available;
    available ^= bit;

    int col = __builtin_ctz(bit);
    current[row] = col;

    uint32_t d1Bit = 1u << ((n - 1 - row) + col);
    uint32_t d2Bit = 1u << (row + col);

    backtrack(row + 1, n, colsMask | bit, d1Mask | d1Bit, d2Mask | d2Bit, allOnes, fixedCol,
              current, solutions);
  }
}

}  // namespace

std::vector<std::vector<int>> solvePreplaced(int n,
                                             const std::vector<std::pair<int, int>>& preplaced) {
  std::vector<std::vector<int>> solutions;
  if (n <= 0 || n > 16) return solutions;

  std::vector<int> fixedCol(n, -1);
  uint32_t colsMask = 0u;
  uint32_t d1Mask = 0u;  // bit ke-((n - 1 - r) + c)
  uint32_t d2Mask = 0u;  // bit ke-(r + c)

  for (const auto& q : preplaced) {
    int r = q.first;
    int c = q.second;
    if (r < 0 || r >= n || c < 0 || c >= n) return solutions;

    // Dua ratu pre-placed di baris yang sama
    if (fixedCol[r] != -1) return solutions;

    uint32_t colBit = 1u << c;
    uint32_t d1Bit = 1u << ((n - 1 - r) + c);
    uint32_t d2Bit = 1u << (r + c);

    // Konflik kolom atau diagonal antar-ratu pre-placed
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
  uint32_t allOnes = (1u << n) - 1u;

  backtrack(0, n, colsMask, d1Mask, d2Mask, allOnes, fixedCol, current, solutions);
  return solutions;
}