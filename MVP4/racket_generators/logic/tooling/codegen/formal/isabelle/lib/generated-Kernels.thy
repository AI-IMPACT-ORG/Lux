theory Kernels
imports lib.generated-Core
begin


(* CLEAN v10 Kernels - Expanded with Logical Operations *)



definition kernel_header_add :: "Term ⇒ Term ⇒ Term" where "kernel_header_add = λ h1 h2 ⇒ h1"

definition kernel_header_product :: "Term ⇒ Term ⇒ Term" where "kernel_header_product = λ h1 h2 ⇒ h1"

definition kernel_header_zero :: "Term ⇒ Term" where "kernel_header_zero = λ k ⇒ k"


definition identity_kernel :: "Term ⇒ Term" where "identity_kernel = λ k ⇒ k"
