#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "CAT.h"

#define VALID_STRING 		"p6pbbUlpLo0BL1bM2k8K"
#define VALID_STRING_SIZE	20

typedef struct {
	char	begin_validation_string[VALID_STRING_SIZE];
	int64_t	value;
	char	end_validation_string[VALID_STRING_SIZE];
} internal_data_t;

static internal_data_t * internal_check_data (CATData v);

CATData CAT_create_signed_value (int64_t value){
	internal_data_t		*d;

	d			= (internal_data_t *) malloc(sizeof(internal_data_t));

	strncpy(d->begin_validation_string, VALID_STRING, VALID_STRING_SIZE);
	strncpy(d->end_validation_string, VALID_STRING, VALID_STRING_SIZE);
	d->value	= value;

	return (CATData) d;
}

int64_t CAT_get_signed_value (CATData v){
	internal_data_t	*d;

	d	= internal_check_data(v);

	return d->value;
}

void CAT_binary_sub (CATData result, CATData v1, CATData v2){
	internal_data_t		*d1;
	internal_data_t		*d2;
	internal_data_t		*dresult;

	d1				= internal_check_data(v1);
	d2				= internal_check_data(v2);
	dresult			= internal_check_data(result);

	dresult->value	= d1->value - d2->value;

	return ;
}

void CAT_binary_add (CATData result, CATData v1, CATData v2){
	internal_data_t		*d1;
	internal_data_t		*d2;
	internal_data_t		*dresult;

	d1				= internal_check_data(v1);
	d2				= internal_check_data(v2);
	dresult			= internal_check_data(result);

	dresult->value	= d1->value + d2->value;

	return ;
}

static internal_data_t * internal_check_data (CATData v){
	internal_data_t	*d;

	if (v == NULL){
		fprintf(stderr, "libCAT: ERROR = input is NULL\n");
		abort();
	}
	d	= (internal_data_t *) v;

	if ( (strncmp(d->begin_validation_string, VALID_STRING, VALID_STRING_SIZE) != 0)		||
			 (strncmp(d->end_validation_string, VALID_STRING, VALID_STRING_SIZE) != 0)		  ){
		fprintf(stderr, "libCAT: ERROR = data has been corrupted\n");
		abort();
	}

	return d;
}
