#include "nqueens.h"
#include <algorithm>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

namespace {

using Board = std::vector<std::pair<int, int>>;

struct RowSegment {
  int row;
  int startCol;
  int endCol;  // eksklusif
};

class WalledSolver {
 public:
  WalledSolver(int n, const std::vector<std::string>& grid)
      : n_(n), grid_(grid), allColsMask_((n == 32) ? 0xFFFFFFFFu : ((1u << n) - 1u)) {
    for (int r = 0; r < n_; ++r) {
      int c = 0;
      while (c < n_) {
        if (grid_[r][c] == 'W') {
          ++c;
        } else {
          int start = c;
          while (c < n_ && grid_[r][c] != 'W') ++c;
          segments_.push_back({r, start, c});
        }
      }
    }

    wallResetCol_.assign(segments_.size(), 0u);
    for (size_t i = 0; i < segments_.size(); ++i) {
      int prevRow = (i == 0) ? -1 : segments_[i - 1].row;
      int currRow = segments_[i].row;
      if (currRow > prevRow) {
        uint32_t wMask = 0u;
        for (int r = prevRow + 1; r <= currRow; ++r) {
          for (int c = 0; c < n_; ++c) {
            if (grid_[r][c] == 'W') wMask |= (1u << c);
          }
        }
        wallResetCol_[i] = wMask;
      }
    }

    colSegmentsRemaining_.assign(segments_.size() + 1, 0);
    int totalColSegs = 0;
    for (int c = 0; c < n_; ++c) {
      int r = 0;
      while (r < n_) {
        if (grid_[r][c] == 'W') {
          ++r;
        } else {
          ++totalColSegs;
          while (r < n_ && grid_[r][c] != 'W') ++r;
        }
      }
    }
    maxBoardCap_ = std::min(static_cast<int>(segments_.size()), totalColSegs);
  }

  std::vector<Board> run() {
    if (n_ <= 0 || n_ > 32) return {};
    dfs(0, -1, 0u, 0u, 0u);
    return std::move(best_);
  }

 private:
  int n_;
  const std::vector<std::string>& grid_;
  uint32_t allColsMask_;
  std::vector<RowSegment> segments_;
  std::vector<uint32_t> wallResetCol_;
  std::vector<int> colSegmentsRemaining_;
  int maxBoardCap_ = 0;

  Board queens_;
  std::vector<Board> best_;
  size_t bestSize_ = 0;

  void advanceRows(int fromRow, int toRow, uint32_t& colMask, uint32_t& d1Mask,
                   uint32_t& d2Mask) const {
    for (int r = fromRow + 1; r <= toRow; ++r) {
      d1Mask = (d1Mask << 1) & allColsMask_;
      d2Mask = (d2Mask >> 1);
      for (int c = 0; c < n_; ++c) {
        if (grid_[r][c] == 'W') {
          uint32_t bit = ~(1u << c);
          colMask &= bit;
          d1Mask &= bit;
          d2Mask &= bit;
        }
      }
    }
  }

  void dfs(size_t segIdx, int lastRow, uint32_t colMask, uint32_t d1Mask, uint32_t d2Mask) {
    int remRowSegs = static_cast<int>(segments_.size() - segIdx);
    if (static_cast<int>(queens_.size()) + remRowSegs < static_cast<int>(bestSize_)) {
      return;
    }

    if (segIdx == segments_.size()) {
      if (queens_.size() > bestSize_) {
        best_.clear();
        bestSize_ = queens_.size();
        best_.push_back(queens_);
        NQ_SNAPSHOT(queens_, "new record: " + std::to_string(bestSize_) + " queens");
      } else if (queens_.size() == bestSize_) {
        best_.push_back(queens_);
        NQ_SNAPSHOT(queens_, "another board with " + std::to_string(bestSize_) + " queens");
      }
      return;
    }

    const RowSegment& seg = segments_[segIdx];
    if (seg.row > lastRow) {
      advanceRows(lastRow, seg.row, colMask, d1Mask, d2Mask);
    }

    uint32_t blocked = colMask | d1Mask | d2Mask;

    
    for (int c = seg.startCol; c < seg.endCol; ++c) {
      uint32_t bit = 1u << c;
      if (!(blocked & bit)) {
        queens_.emplace_back(seg.row, c);
        dfs(segIdx + 1, seg.row, colMask | bit, d1Mask | bit, d2Mask | bit);
        queens_.pop_back();
      }
    }

    if (static_cast<int>(queens_.size()) + (remRowSegs - 1) >= static_cast<int>(bestSize_)) {
      dfs(segIdx + 1, seg.row, colMask, d1Mask, d2Mask);
    }
  }
};

}

std::vector<std::vector<std::pair<int, int>>> solveWalled(int n,
                                                          const std::vector<std::string>& grid) {
  return WalledSolver(n, grid).run();
}