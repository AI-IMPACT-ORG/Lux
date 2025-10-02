inductive CleanSort : Type where | L | B | R | I
inductive Term : Type where | ConstL | ConstB | ConstR | ConstI | PlusB Term Term | MultB Term Term

def CLEAN_Sort : Type := CleanSort
def CLEAN_Term : Type := Term
def CLEAN_PlusB : Term → Term → Term := Term.PlusB

-- CLEAN v10 Main Library - Unified Interface
