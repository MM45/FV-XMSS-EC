# -*- Makefile -*-

# Environment/Setup
## Docker
DOCKER_BIN ?= docker
DOCKER_IMAGE ?= fv-xmss-ec:r2026.02
DOCKER_TTY ?= -t

## EasyCrypt
EC_BIN ?= easycrypt
EC_PROOFS_ROOT ?= proofs

### Runtest
EC_RUNTEST_ENV ?=
EC_RUNTEST_FILE ?= config/tests.config
EC_RUNTEST_JOBS ?= 1
EC_RUNTEST_REPORT_DIR ?= reports

EC_RUNTEST_OPTS = -jobs $(EC_RUNTEST_JOBS)
EC_RUNTEST = $(strip $(EC_RUNTEST_ENV) $(EC_BIN) runtest $(EC_RUNTEST_OPTS) $(EC_RUNTEST_FILE))


## Special
.DEFAULT_GOAL := check


# Targets
## Docker
docker-check: docker-run

docker-safe:
	@if [ -f /.dockerenv ]; then \
		echo "Error: Docker target invoked inside a (Docker) container."; \
		exit 2; \
	fi
	@$(DOCKER_BIN) info >/dev/null 2>&1 || { \
		echo "Error: Docker daemon unresponsive. Ensure it is running and you have the appropriate permissions."; \
		exit 2; \
	}

docker-build: docker-safe
	$(DOCKER_BIN) build -t $(DOCKER_IMAGE) .

docker-run: docker-build
	$(DOCKER_BIN) run --rm $(DOCKER_TTY) $(DOCKER_IMAGE)

docker-shell: docker-build
	$(DOCKER_BIN) run --rm -it $(DOCKER_IMAGE) bash


## EasyCrypt
check: check-default

check-%: FORCE
	@echo "Creating $(EC_RUNTEST_REPORT_DIR) directory if it does not exist yet..."
	@mkdir -p "$(EC_RUNTEST_REPORT_DIR)"
	@echo "Starting test $*..."
	$(EC_RUNTEST) -report "$(EC_RUNTEST_REPORT_DIR)/$*.log" $*

clean:
	@echo "Removing EasyCrypt's cached verification results ('.eco' files)..."
	@if [ -d "$(EC_PROOFS_ROOT)" ]; then \
		find "$(EC_PROOFS_ROOT)" -type f -name '*.eco' -exec rm -f '{}' + ; \
	fi

dry-clean:
	@echo "make clean would remove the following files..."
	@if [ -d "$(EC_PROOFS_ROOT)" ]; then \
		find "$(EC_PROOFS_ROOT)" -type f -name '*.eco' -print ; \
	fi

clobber: clean
	@echo "Removing $(EC_RUNTEST_REPORT_DIR) directory"
	@rm -rf "$(EC_RUNTEST_REPORT_DIR)"

FORCE:

## Help
help:
	@printf "\n"
	@printf "Usage:\n"
	@printf "  make <target>\n\n"

	@printf "Main targets:\n"
	@printf "  %-18s %s\n"   "docker-check" "Run all EasyCrypt tests in Docker."
	@printf "  %-18s %s\n"   "check"        "Run all EasyCrypt tests."
	@printf "  %-18s %s\n\n" "clean"        "Remove EasyCrypt's cached verification results (*.eco files)."

	@printf "Miscellaneous targets:\n"
	@printf "  %-18s %s\n" "docker-safe"  "Check if it is safe to run Docker targets."
	@printf "  %-18s %s\n" "docker-build" "Build Docker image ($(DOCKER_IMAGE))."
	@printf "  %-18s %s\n" "docker-run"   "Run Docker image ($(DOCKER_IMAGE)), equivalent to 'docker-check'."
	@printf "  %-18s %s\n" "docker-shell" "Start an interactive shell in Docker (instead of running tests)."
	@printf "  %-18s %s\n" "check-<name>" "Run a specific EasyCrypt test."
	@printf "  %-18s %s\n" "dry-clean"    "Show what 'make clean' would remove."
	@printf "  %-18s %s\n" "clobber"      "clean + remove $(EC_RUNTEST_REPORT_DIR) directory."

## Special
.PHONY: docker-check docker-safe docker-build docker-run docker-shell
.PHONY: check clean dry-clean clobber FORCE
.PHONY: help
.NOTPARALLEL:
