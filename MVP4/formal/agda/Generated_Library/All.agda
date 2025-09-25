module Generated_Library.All where

-- BootstrapPaper: Complete Formal Verification Library
-- This module provides a single import point for all BootstrapPaper components
-- Use this module in downstream Agda developments to access the entire library

-- Core Foundations
open import BootstrapPaper.Foundations.M3 public

-- Operators and Transformations  
open import BootstrapPaper.Operators.RG public

-- Test Suite and Verification
open import BootstrapPaper.Tests.Core public

-- Main Library (re-exports everything)
open import Generated_Library.BootstrapPaper public

-- Library Documentation
-- ===================
-- 
-- This library provides a complete formal verification framework based on:
-- 1. M3 Metametamodel Foundation - Core mathematical structures
-- 2. RG Operators - Renormalization Group transformations
-- 3. Test Suite - Verification and validation tools
--
-- Key Features:
-- - All moduli parameters are explicitly resolved with concrete values
-- - Type-safe data constructors and operations
-- - Complete MDE pyramid implementation (M3→M2→M1)
-- - Mathematical theorem helpers (Gödel, Tarski, Rice, Noether, Ward)
-- - Comprehensive test suite for validation
--
-- Usage in Downstream Developments:
-- ==================================
-- 
-- To use this library in your Agda development:
-- 1. Add this directory to your Agda library path
-- 2. Import this module: open import Generated_Library.All
-- 3. Access components through the public exports
--
-- Example:
-- ```agda
-- module MyDevelopment where
--   open import Generated_Library.All
--   
--   -- Now you have access to all BootstrapPaper components
--   my-function : ModuliSpace → Bool
--   my-function ms = anomaly-vanishes-at-m3 (record { ports = [] ; kinds = [] ; arity-map = _ ; src-sorts = _ ; dst-sorts = _ })
-- ```
