/*---------------------------------------------------------------------------
  Copyright 2021 Microsoft Corporation.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the file "license.txt" at the root of this distribution.
---------------------------------------------------------------------------*/

#pragma clang diagnostic ignored "-Wdisabled-macro-expansion"
#define PCRE2_CODE_UNIT_WIDTH 8
#include <pcre2.h>

static kk_string_t kk_regex_version(kk_context_t* ctx) {
  char ver[256];
  int res = pcre2_config(PCRE2_CONFIG_VERSION, &ver);
  return kk_string_alloc_from_qutf8(ver, ctx);
}

static void kk_regex_free( void* pre, kk_block_t* b ) {
  kk_info_message( "free regex\n" );
  pcre2_code* re = (pcre2_code*)pre;
  if (re != NULL) pcre2_code_free(re);
}

static kk_box_t kk_regex_create( kk_string_t pat, int32_t ignore_case, int32_t multi_line, kk_context_t* ctx ) {
  kk_ssize_t len;
  const char* cpat = kk_string_cbuf_borrow( pat, &len );
  PCRE2_SIZE errofs = 0;
  int        errnum = 0;
  pcre2_code* re = pcre2_compile( cpat, PCRE2_ZERO_TERMINATED, 0, &errnum, &errofs, NULL /* compile context */);
  kk_info_message( "create regex: %i, %p\n", errnum, re );
  kk_string_drop(pat,ctx);
  return kk_cptr_raw_box( &kk_regex_free, re, ctx );
}

static void kk_match_data_free( void* pmd, kk_block_t* b ) {
  kk_info_message( "free match_data\n" );
  pcre2_match_data* md = (pcre2_match_data*)pmd;
  if (md != NULL) pcre2_match_data_free(md);
}

static kk_std_core_types__maybe kk_regex_exec( kk_box_t bre, kk_string_t str, kk_ssize_t start, kk_context_t* ctx ) {
  kk_info_message( "regex_exec\n" );
  pcre2_code* re = (pcre2_code*)kk_cptr_raw_unbox(bre);
  if (re == NULL) goto nothing;    
  pcre2_match_data* match_data = pcre2_match_data_create_from_pattern(re, NULL);
  if (match_data==NULL) goto nothing;  
  kk_ssize_t len;
  const char* cstr = kk_string_cbuf_borrow(str, &len );  
  kk_info_message( "match...\n" );
  int rc = pcre2_match( re, cstr, len, start, 0 /* options */, match_data, NULL /* match context */ );
  if (rc <= 0) {
    goto nothing;
  }
  PCRE2_SIZE* ovector = pcre2_get_ovector_pointer(match_data);
  PCRE2_SIZE  start0  = ovector[0];
  PCRE2_SIZE  len0    = ovector[1] - ovector[0];
  kk_box_t bmd = kk_cptr_raw_box( &kk_match_data_free, match_data, ctx );
  
  kk_info_message( "create matched: slice %zi %zi\n", start0, len0 );
  kk_std_text_regex__matched matched = 
    kk_std_text_regex__new_Matched( kk_reuse_null, 
                                    kk_std_core__new_Sslice( str, kk_to_ssize_t(start0), kk_to_ssize_t(len0), ctx ), 
                                    kk_std_text_regex__new_Groups(bmd, ctx), ctx );
  kk_string_drop(str,ctx);
  kk_box_drop(bre,ctx);
  return kk_std_core_types__new_Just( kk_std_text_regex__matched_box(matched, ctx), ctx );

nothing:
  kk_info_message( "exec: nothing\n" );
  kk_string_drop(str,ctx);
  kk_box_drop(bre,ctx);
  return kk_std_core_types__new_Nothing(ctx);
}