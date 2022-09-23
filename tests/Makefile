IDRIS2 ?= idris2
PACK ?= pack

INTERACTIVE ?= --interactive

threads ?= `nproc`

TESTS_PACKAGE = tests.ipkg

TEST_CMD_ARG = bash -c '$(PACK) install-deps >/dev/null && $(IDRIS2) "$@"' --

TESTS_RUNNER = $(PACK) run $(TESTS_PACKAGE) "$(TEST_CMD_ARG)" $(INTERACTIVE) --timing --failure-file failures --threads $(threads)

.PHONY: all runner test retest clean

all: test

runner:
	${PACK} build $(TESTS_PACKAGE)

test: runner
	$(TESTS_RUNNER) --only "$(only)"

retest: runner
	$(TESTS_RUNNER) --only-file failures

clean:
	${PACK} clean $(TESTS_PACKAGE)
	$(RM) failures
	@find . -depth -type d -name build -exec rm -rf '{}' \;
	@find . -type f -name 'output' -delete
	@find . -type f -name '*.ttc'  -delete
	@find . -type f -name '*.ttm'  -delete
	@find . -type f -name '*.ibc'  -delete
