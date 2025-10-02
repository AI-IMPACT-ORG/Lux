module lib.CLEAN where

open import lib.generated-Core
open import lib.generated-Observers
open import lib.generated-Kernels
open import lib.generated-NormalForms

CLEAN_Sort : Set
CLEAN_Sort = Sort

CLEAN_Term : Set
CLEAN_Term = Term

CLEAN_PlusB : Term → Term → Term
CLEAN_PlusB = TermPlusB

-- CLEAN v10 Main Library - Unified Interface
