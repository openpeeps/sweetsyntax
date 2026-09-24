# SIMD codegen flags are per-architecture (mirrors openparser's
# tests/test_fuzzy.nims pattern).
#
# x86-64: AVX2 is opt-in via -d:avx2. The -mavx2 C flag must travel with it
# because nimsimd/avx2 intrinsics need the ISA enabled at C compile time.
# Passing -mavx2 unconditionally breaks ARM64 builds (clang rejects it).
when defined(amd64):
  --define:avx2
  --passC:"-mavx2"
  --passL:"-mavx2"
elif defined(arm64):
  # ARM64 (AArch64) always has NEON: nimsimd/neon (arm_neon.h) compiles with
  # no extra C flag, and openparser selects its NEON lanes on defined(arm64)
  # alone. This define exists so ARM builds get an explicit SIMD opt-in
  # symmetric to -d:avx2 on x86-64.
  --define:neon