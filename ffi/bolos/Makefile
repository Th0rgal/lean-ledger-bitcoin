# ffi/bolos Makefile — automated host + ARM Thumb cross-compile & C unit tests
# for the lean-ledger-bitcoin BOLOS FFI shim.
#
# `make test`:
#   1. builds and RUNS the host C unit test, linked against the turbo-lean
#      emitted host freestanding archive (build/host/liblean_ledger_bitcoin.a),
#      verifying llb_version_packed == 0x00020401 and every shim wrapper
#      (including fail-closed paths) against a deterministic mock BOLOS TCB;
#   2. cross-compiles the shim + freestanding test with
#      `clang --target=thumbv6m-none-eabi` (Nano X),
#      `clang --target=thumbv8m.main-none-eabi` (Nano S+ / Stax / Flex / Apex P)
#      and `arm-none-eabi-gcc` (BOLOS SDK toolchain), links each against the
#      matching emitted archive and verifies 0 undefined symbols with the
#      kernel entry (`llb_version_packed`) present in the linked image.
#
# Prerequisite: run `scripts/build-freestanding.sh` from the repository root
# first (it fills ffi/bolos/build/{host,thumbv6m,thumbv8m.main}).

CC ?= cc
CLANG ?= clang
HUB ?= /var/lib/orb-node/work/caches/ledger-hub
LLVM_NM ?= llvm-nm
BUILD_DIR := build
HOST_DIR := $(BUILD_DIR)/host
V6M_DIR := $(BUILD_DIR)/thumbv6m
V8M_DIR := $(BUILD_DIR)/thumbv8m.main
LIB_NAME := liblean_ledger_bitcoin

ARM_GCC ?= $(shell command -v arm-none-eabi-gcc 2>/dev/null || echo "$(HUB)/sysroot/usr/bin/arm-none-eabi-gcc")

# Cross flags shared by the clang and arm-none-eabi-gcc thumb builds: pure
# freestanding C99, no libc (the test provides its own memset/memcpy).
CROSS_CFLAGS := -std=c99 -Wall -Wextra -Werror -ffreestanding -fno-builtin \
                -fstack-usage -DLLB_TEST_FREESTANDING -I.

HOST_BIN := $(BUILD_DIR)/test_bolos_ffi_host
V6M_CLANG_ELF := $(BUILD_DIR)/test_bolos_ffi_thumbv6m_clang.elf
V8M_CLANG_ELF := $(BUILD_DIR)/test_bolos_ffi_thumbv8m_clang.elf
V6M_GCC_ELF := $(BUILD_DIR)/test_bolos_ffi_thumbv6m_arm_gcc.elf

HOST_OBJS := $(BUILD_DIR)/host_llb_bolos_shim.o $(BUILD_DIR)/host_test_bolos_ffi.o
V6M_CLANG_OBJS := $(BUILD_DIR)/v6m_clang_llb_bolos_shim.o $(BUILD_DIR)/v6m_clang_test_bolos_ffi.o
V8M_CLANG_OBJS := $(BUILD_DIR)/v8m_clang_llb_bolos_shim.o $(BUILD_DIR)/v8m_clang_test_bolos_ffi.o
V6M_GCC_OBJS := $(BUILD_DIR)/v6m_gcc_llb_bolos_shim.o $(BUILD_DIR)/v6m_gcc_test_bolos_ffi.o

.PHONY: all test clean
all: test

$(HOST_DIR)/$(LIB_NAME).a $(V6M_DIR)/$(LIB_NAME).a $(V8M_DIR)/$(LIB_NAME).a:
	@echo "ffi/bolos: missing freestanding archive $@." >&2
	@echo "  Run scripts/build-freestanding.sh from the repository root first." >&2
	@exit 1

# --- 1) host build & run ------------------------------------------------

$(BUILD_DIR)/host_llb_bolos_shim.o: llb_bolos_shim.c llb_bolos_shim.h $(HOST_DIR)/$(LIB_NAME).a | $(BUILD_DIR)
	$(CC) -std=c99 -Wall -Wextra -Werror -I$(HOST_DIR) -c $< -o $@

$(BUILD_DIR)/host_test_bolos_ffi.o: test_bolos_ffi.c llb_bolos_shim.h $(HOST_DIR)/$(LIB_NAME).a | $(BUILD_DIR)
	$(CC) -std=c99 -Wall -Wextra -Werror -I$(HOST_DIR) -c $< -o $@

$(HOST_BIN): $(HOST_OBJS) $(HOST_DIR)/$(LIB_NAME).a
	$(CC) $(HOST_OBJS) $(HOST_DIR)/$(LIB_NAME).a -o $@

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

host-test: $(HOST_BIN)
	$(HOST_BIN)

# --- 2) ARM Thumb cross builds (link-only verification; no emulator) ------

$(BUILD_DIR)/v6m_clang_%.o: %.c llb_bolos_shim.h $(V6M_DIR)/$(LIB_NAME).a | $(BUILD_DIR)
	$(CLANG) --target=thumbv6m-none-eabi -mcpu=cortex-m0 $(CROSS_CFLAGS) -I$(V6M_DIR) -c $< -o $@

$(BUILD_DIR)/v8m_clang_%.o: %.c llb_bolos_shim.h $(V8M_DIR)/$(LIB_NAME).a | $(BUILD_DIR)
	$(CLANG) --target=thumbv8m.main-none-eabi -mcpu=cortex-m33 $(CROSS_CFLAGS) -I$(V8M_DIR) -c $< -o $@

$(BUILD_DIR)/v6m_gcc_%.o: %.c llb_bolos_shim.h $(V6M_DIR)/$(LIB_NAME).a | $(BUILD_DIR)
	$(ARM_GCC) -mcpu=cortex-m0 -mthumb $(CROSS_CFLAGS) -I$(V6M_DIR) -c $< -o $@

$(V6M_CLANG_ELF): $(V6M_CLANG_OBJS) $(V6M_DIR)/$(LIB_NAME).a
	$(CLANG) --target=thumbv6m-none-eabi -nostdlib -Wl,-e,main -o $@ $(V6M_CLANG_OBJS) $(V6M_DIR)/$(LIB_NAME).a

$(V8M_CLANG_ELF): $(V8M_CLANG_OBJS) $(V8M_DIR)/$(LIB_NAME).a
	$(CLANG) --target=thumbv8m.main-none-eabi -nostdlib -Wl,-e,main -o $@ $(V8M_CLANG_OBJS) $(V8M_DIR)/$(LIB_NAME).a

$(V6M_GCC_ELF): $(V6M_GCC_OBJS) $(V6M_DIR)/$(LIB_NAME).a
	$(ARM_GCC) -mcpu=cortex-m0 -mthumb -ffreestanding -nostdlib -Wl,-e,main -o $@ $(V6M_GCC_OBJS) $(V6M_DIR)/$(LIB_NAME).a

# Verifies 0 undefined symbols and that the linked image still carries the
# freestanding kernel ABI symbol llb_version_packed (whose packed value
# 0x00020401 is verified at runtime by the host test).
define verify_elf
	@undef="$$($(LLVM_NM) $(1) | awk '$$1 == "U" || $$2 == "U"')"; \
	if [ -n "$$undef" ]; then \
		echo "ffi/bolos: $(1) has undefined symbols: $$undef" >&2; exit 1; \
	fi; \
	if ! $(LLVM_NM) $(1) | grep -q ' T llb_version_packed'; then \
		echo "ffi/bolos: $(1) missing llb_version_packed" >&2; exit 1; \
	fi; \
	echo "ffi/bolos: $(1) linked clean (0 undefined symbols, llb_version_packed present)"
endef

cross-thumbv6m-clang: $(V6M_CLANG_ELF)
	$(call verify_elf,$(V6M_CLANG_ELF))

cross-thumbv8m-clang: $(V8M_CLANG_ELF)
	$(call verify_elf,$(V8M_CLANG_ELF))

cross-thumbv6m-arm-gcc: $(V6M_GCC_ELF)
	$(call verify_elf,$(V6M_GCC_ELF))

test: host-test cross-thumbv6m-clang cross-thumbv8m-clang cross-thumbv6m-arm-gcc
	@echo "ffi/bolos: ALL TESTS PASSED (host runtime + 3 ARM Thumb cross links)"

clean:
	rm -rf $(BUILD_DIR)
