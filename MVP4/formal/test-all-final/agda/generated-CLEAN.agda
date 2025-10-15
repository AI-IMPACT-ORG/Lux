module CLEAN where

open import lib.generated_Core
open import lib.generated_Observers
open import lib.generated_Kernels
open import lib.generated_NormalForms

-- CLEAN v10 Main Library - Unified Interface

CLEAN_Sort : Type
CLEAN_Sort = Sort
CLEAN_Term : Type
CLEAN_Term = Term
CLEAN_PlusB : Term → Term → Term
CLEAN_PlusB = TermPlusB

