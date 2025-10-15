# Metamath verification helpers (layered in architectural order)

METAMATH_KNIFE ?= /Users/rutgerboels/.cargo/bin/metamath-knife

METAMATH_LAYER_FILES ?= \
	metamath/clean/core/base.mm \
	metamath/clean/core/signature.mm \
	metamath/clean/core/diagram.mm \
	metamath/clean/core/normalform.mm \
	metamath/clean/core/rewrite.mm \
	metamath/clean/core/moduli.mm \
	metamath/clean/core/renormalisation.mm \
	metamath/clean/app/plbridge.mm \
	metamath/clean/app/classification.mm \
	metamath/clean/app/complexity.mm \
	metamath/clean/app/kernel.mm \
	metamath/clean/app/guarded_pipeline.mm \
	metamath/clean/ports/boolean.mm \
	metamath/clean/ports/analytic.mm \
	metamath/clean/ports/analytic_zeta.mm \
	metamath/clean/library.mm \
	../metamath/CLEAN_V10_Framework.mm \
	../metamath/CLEAN_V10_Class.mm

.PHONY: mm-verify
mm-verify:
	@set -e; \
	for db in $(METAMATH_LAYER_FILES); do \
		dir=$$(dirname "$$db"); \
		base=$$(basename "$$db"); \
		echo "(cd $$dir && \"$(METAMATH_KNIFE)\" -v $$base)"; \
		( cd "$$dir" && "$(METAMATH_KNIFE)" -v "$$base" ); \
	done
