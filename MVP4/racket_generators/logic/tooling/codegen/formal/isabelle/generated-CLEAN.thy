theory CLEAN
imports Main
begin

datatype Sort = L | B | R | I
datatype Term = ConstL | ConstB | ConstR | ConstI | PlusB Term Term | MultB Term Term

definition CLEAN_Sort :: "Sort" where "CLEAN_Sort = L"
definition CLEAN_Term :: "Term" where "CLEAN_Term = ConstB"
definition CLEAN_PlusB :: "Term => Term => Term" where "CLEAN_PlusB = PlusB"

end

(* CLEAN v10 Main Library - Unified Interface *)
