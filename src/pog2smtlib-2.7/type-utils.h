#ifndef TYPE_UTILS_H
#define TYPE_UTILS_H

#include "btype.h"

inline const BType& elementType(const BType& type) {
  return type.toPowerType().content;
}

#endif
