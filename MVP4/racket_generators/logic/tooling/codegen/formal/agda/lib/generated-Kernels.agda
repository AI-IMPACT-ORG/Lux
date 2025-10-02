module lib.Kernels where
open import lib.generated-Core

-- CLEAN v10 Kernels - Expanded with Logical Operations



kernel_header_add : Term → Term → Term
kernel_header_add = λ h1 h2 → h1

kernel_header_product : Term → Term → Term
kernel_header_product = λ h1 h2 → h1

kernel_header_zero : Term → Term
kernel_header_zero = λ k → k


identity_kernel : Term → Term
identity_kernel = λ k → k
