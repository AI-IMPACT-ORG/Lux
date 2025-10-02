Require Import Core.


(* CLEAN v10 Kernels - Expanded with Logical Operations *)

Definition kernel_compose : Kernel -> Kernel -> Kernel :=
  fun k1 k2 => k1.

Definition kernel_apply : Kernel -> Term -> Term :=
  fun k t => t.

Definition kernel_identity : Kernel :=
  KernelId.

Definition kernel_header_add : Kernel -> Header -> Header -> Kernel :=
  fun k h1 h2 => k.

Definition kernel_header_product : Kernel -> Header -> Header -> Kernel :=
  fun k h1 h2 => k.

Definition kernel_header_zero : Kernel -> Kernel :=
  fun k => KernelId.

Definition identity_kernel : Kernel :=
  KernelId.
