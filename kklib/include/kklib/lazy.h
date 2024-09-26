#pragma once
#ifndef KK_LAZY_H
#define KK_LAZY_H
/*---------------------------------------------------------------------------
  Copyright 2024, Microsoft Research, Daan Leijen, Anton Lorenzen

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

kk_decl_export bool kk_lazy_atomic_enter(kk_datatype_t lazy, kk_context_t* ctx);
kk_decl_export void kk_lazy_atomic_unblock(kk_datatype_t lazy, kk_context_t* ctx);

static inline bool kk_is_lazy_con( kk_datatype_t lazy, kk_context_t* ctx ) {
  return (kk_datatype_is_ptr(lazy) && kk_datatype_ptr_tag(lazy,ctx) >= KK_TAG_LAZY);
}

static inline bool kk_is_thread_shared( kk_datatype_ptr_t lazy, kk_context_t* ctx ) {
  kk_assert(kk_is_lazy_con(lazy,ctx));
  return kk_block_is_thread_shared(kk_datatype_as_ptr(lazy,ctx));
}


#endif // KK_LAZY_H
