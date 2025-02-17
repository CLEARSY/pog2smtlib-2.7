#ifndef BCONSTRUCT_HASH_H
#define BCONSTRUCT_HASH_H

#include <cstddef>
#include <memory>

#include "bconstruct.h"

namespace BConstruct {

struct PtrHash {
  std::size_t operator()(const std::shared_ptr<BConstruct::Abstract> &t) const {
    return t->hash();
  }
};

struct PtrCompare {
  bool operator()(const std::shared_ptr<BConstruct::Abstract> &a,
                  const std::shared_ptr<BConstruct::Abstract> &b) const {
    return *a < *b;
  }
};

struct PtrEqual {
  bool operator()(const std::shared_ptr<BConstruct::Abstract> &a,
                  const std::shared_ptr<BConstruct::Abstract> &b) const {
    return *a == *b;
  }
};

};  // namespace BConstruct

#endif  // BCONSTRUCT_HASH_H
