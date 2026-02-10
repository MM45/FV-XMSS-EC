# -*- Makefile -*-

# Environment/Setup
## EasyCrypt
EC_BIN ?= easycrypt
EC_PROOFS_ROOT ?= proofs

### Runtest
EC_RUNTEST_ENV ?=
EC_RUNTEST_FILE ?= config/tests.config
EC_RUNTEST_JOBS ?= 2
EC_RUNTEST_REPORT_DIR ?= reports

EC_RUNTEST_OPTS = -jobs $(EC_RUNTEST_JOBS)
EC_RUNTEST = $(strip $(EC_RUNTEST_ENV) $(EC_BIN) runtest $(EC_RUNTEST_OPTS) $(EC_RUNTEST_FILE))


## Special
.DEFAULT_GOAL := check


# Targets
## Actual
check: check_default

check_%: FORCE
	@echo "Creating directory for EasyCrypt's test reports if it does not exist yet"
	@mkdir -p "$(EC_RUNTEST_REPORT_DIR)"
	@echo "Starting test $(subst _,-,$*)..."
	$(EC_RUNTEST) -report "$(EC_RUNTEST_REPORT_DIR)/$(subst _,-,$*).log" $(subst _,-,$*)

clean:
	@echo "Removing EasyCrypt's cached verification results ('.eco' files)"
	@find "$(EC_PROOFS_ROOT)" -type f -name '*.eco' -exec rm -f '{}' +

dry_clean:
	@echo "make clean would remove the following files"
	@find "$(EC_PROOFS_ROOT)" -type f -name '*.eco' -print

clobber: clean
	@echo "Removing directory with EasyCrypt's test reports ($(EC_RUNTEST_REPORT_DIR)/)"
	@rm -rf "$(EC_RUNTEST_REPORT_DIR)"

FORCE:

## Special
.PHONY: check clean dry_clean clobber FORCE
.NOTPARALLEL:
