#ifndef CAT_H
#define CAT_H

#include <stdint.h>

typedef void * CATData;

CATData CAT_create_signed_value (int64_t value);

int64_t CAT_get_signed_value (CATData v);

void CAT_binary_add (CATData result, CATData v1, CATData v2);

void CAT_binary_sub (CATData result, CATData v1, CATData v2);

#endif
