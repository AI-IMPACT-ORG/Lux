module CLEAN where

open import lib.Core
open import lib.Observers
open import lib.Kernels
open import lib.NormalForms

-- CLEAN v10 Main Library - Simplified

CLEAN-Sort : Set
CLEAN-Sort = Sort

CLEAN-Term : Set
CLEAN-Term = Term

CLEAN-PlusB : Term → Term → Term
CLEAN-PlusB = PlusB

