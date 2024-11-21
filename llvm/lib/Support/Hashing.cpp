//===-------------- lib/Support/Hashing.cpp -------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file provides implementation bits for the LLVM common hashing
// infrastructure. Documentation and most of the other information is in the
// header file.
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Hashing.h"

using namespace llvm;

// Definition and static initializer for the fixed seed. This initializer
// should always be zero to ensure its value can never appear to be non-zero,
// even during dynamic initialization.
std::atomic<uint64_t> llvm::hashing::detail::fixed_seed_override = 0;

// Function for forced setting of the fixed seed.
void llvm::set_fixed_execution_hash_seed(uint64_t fixed_value) {
  hashing::detail::fixed_seed_override = fixed_value;
}
