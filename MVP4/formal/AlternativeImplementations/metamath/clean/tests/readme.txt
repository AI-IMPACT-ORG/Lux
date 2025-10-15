Metamath test scripts for the CLEAN port.
----------------------------------------

Populate this directory with `.mm` snippets that type-check concrete
examples (e.g., loading the boolean port and instantiating a sample
rewrite).  Tests should depend only on exported library interfaces.

Suggested layout:
  - sanity.mm  : minimal load to ensure include order works
  - boolean.mm : exercises the boolean adapter end-to-end
  - analytic.mm: stubs for analytic number theory checks once axioms set
