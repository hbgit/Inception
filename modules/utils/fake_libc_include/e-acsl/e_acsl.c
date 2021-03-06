/**************************************************************************/
/*                                                                        */
/*  This file is part of the Frama-C's E-ACSL plug-in.                    */
/*                                                                        */
/*  Copyright (C) 2012-2014                                               */
/*    CEA (Commissariat � l'�nergie atomique et aux �nergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file licenses/LGPLv2.1).            */
/*                                                                        */
/**************************************************************************/

#include "e_acsl.h"
#include <stdlib.h>
#include <stdio.h>

void e_acsl_assert(int predicate, 
		   char *kind, 
		   char *fct, 
		   char *pred_txt, 
		   int line) 
{
  if (! predicate) {
    printf("%s failed at line %d in function %s.\n\
The failing predicate is:\n%s.\n",
	   kind, line, fct, pred_txt);
    exit(1);
  }
}
