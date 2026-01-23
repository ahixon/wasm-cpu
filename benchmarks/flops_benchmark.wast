;; FLOPS Benchmark - Regular and Vectorized (SIMD)
;;
;; This benchmark measures floating-point operations per second for:
;; - Scalar f32 operations
;; - Scalar f64 operations
;; - SIMD f32x4 operations (4 floats per vector)
;; - SIMD f64x2 operations (2 doubles per vector)
;;
;; Each benchmark function performs a fixed number of FLOPs and returns
;; a checksum value to prevent dead code elimination.

(module
  ;; ============================================================
  ;; SCALAR F32 BENCHMARK
  ;; Performs N iterations of 8 f32 operations each (4 mul + 4 add)
  ;; Total FLOPs = N * 8
  ;; ============================================================
  (func (export "bench_f32_scalar") (param $iterations i32) (result f32)
    (local $i i32)
    (local $acc0 f32)
    (local $acc1 f32)
    (local $acc2 f32)
    (local $acc3 f32)
    (local $c1 f32)
    (local $c2 f32)

    ;; Initialize accumulators
    (local.set $acc0 (f32.const 1.0))
    (local.set $acc1 (f32.const 1.1))
    (local.set $acc2 (f32.const 1.2))
    (local.set $acc3 (f32.const 1.3))

    ;; Constants for operations (chosen to avoid overflow/underflow)
    (local.set $c1 (f32.const 1.0000001))
    (local.set $c2 (f32.const 0.9999999))

    ;; Main loop
    (local.set $i (i32.const 0))
    (block $break
      (loop $continue
        (br_if $break (i32.ge_u (local.get $i) (local.get $iterations)))

        ;; 4 multiplications
        (local.set $acc0 (f32.mul (local.get $acc0) (local.get $c1)))
        (local.set $acc1 (f32.mul (local.get $acc1) (local.get $c1)))
        (local.set $acc2 (f32.mul (local.get $acc2) (local.get $c1)))
        (local.set $acc3 (f32.mul (local.get $acc3) (local.get $c1)))

        ;; 4 additions
        (local.set $acc0 (f32.add (local.get $acc0) (local.get $c2)))
        (local.set $acc1 (f32.add (local.get $acc1) (local.get $c2)))
        (local.set $acc2 (f32.add (local.get $acc2) (local.get $c2)))
        (local.set $acc3 (f32.add (local.get $acc3) (local.get $c2)))

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $continue)
      )
    )

    ;; Return sum of accumulators as checksum
    (f32.add
      (f32.add (local.get $acc0) (local.get $acc1))
      (f32.add (local.get $acc2) (local.get $acc3))
    )
  )

  ;; ============================================================
  ;; SCALAR F64 BENCHMARK
  ;; Performs N iterations of 8 f64 operations each (4 mul + 4 add)
  ;; Total FLOPs = N * 8
  ;; ============================================================
  (func (export "bench_f64_scalar") (param $iterations i32) (result f64)
    (local $i i32)
    (local $acc0 f64)
    (local $acc1 f64)
    (local $acc2 f64)
    (local $acc3 f64)
    (local $c1 f64)
    (local $c2 f64)

    ;; Initialize accumulators
    (local.set $acc0 (f64.const 1.0))
    (local.set $acc1 (f64.const 1.1))
    (local.set $acc2 (f64.const 1.2))
    (local.set $acc3 (f64.const 1.3))

    ;; Constants for operations
    (local.set $c1 (f64.const 1.00000000001))
    (local.set $c2 (f64.const 0.99999999999))

    ;; Main loop
    (local.set $i (i32.const 0))
    (block $break
      (loop $continue
        (br_if $break (i32.ge_u (local.get $i) (local.get $iterations)))

        ;; 4 multiplications
        (local.set $acc0 (f64.mul (local.get $acc0) (local.get $c1)))
        (local.set $acc1 (f64.mul (local.get $acc1) (local.get $c1)))
        (local.set $acc2 (f64.mul (local.get $acc2) (local.get $c1)))
        (local.set $acc3 (f64.mul (local.get $acc3) (local.get $c1)))

        ;; 4 additions
        (local.set $acc0 (f64.add (local.get $acc0) (local.get $c2)))
        (local.set $acc1 (f64.add (local.get $acc1) (local.get $c2)))
        (local.set $acc2 (f64.add (local.get $acc2) (local.get $c2)))
        (local.set $acc3 (f64.add (local.get $acc3) (local.get $c2)))

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $continue)
      )
    )

    ;; Return sum of accumulators as checksum
    (f64.add
      (f64.add (local.get $acc0) (local.get $acc1))
      (f64.add (local.get $acc2) (local.get $acc3))
    )
  )

  ;; ============================================================
  ;; SIMD F32X4 BENCHMARK (Vectorized)
  ;; Performs N iterations of 8 vector operations each (4 mul + 4 add)
  ;; Each vector op processes 4 floats simultaneously
  ;; Total FLOPs = N * 8 * 4 = N * 32
  ;; ============================================================
  (func (export "bench_f32x4_simd") (param $iterations i32) (result v128)
    (local $i i32)
    (local $acc0 v128)
    (local $acc1 v128)
    (local $acc2 v128)
    (local $acc3 v128)
    (local $c1 v128)
    (local $c2 v128)

    ;; Initialize accumulators with different starting values per lane
    (local.set $acc0 (v128.const f32x4 1.0 1.1 1.2 1.3))
    (local.set $acc1 (v128.const f32x4 1.4 1.5 1.6 1.7))
    (local.set $acc2 (v128.const f32x4 1.8 1.9 2.0 2.1))
    (local.set $acc3 (v128.const f32x4 2.2 2.3 2.4 2.5))

    ;; Constants for operations
    (local.set $c1 (v128.const f32x4 1.0000001 1.0000001 1.0000001 1.0000001))
    (local.set $c2 (v128.const f32x4 0.9999999 0.9999999 0.9999999 0.9999999))

    ;; Main loop
    (local.set $i (i32.const 0))
    (block $break
      (loop $continue
        (br_if $break (i32.ge_u (local.get $i) (local.get $iterations)))

        ;; 4 vector multiplications (16 scalar muls)
        (local.set $acc0 (f32x4.mul (local.get $acc0) (local.get $c1)))
        (local.set $acc1 (f32x4.mul (local.get $acc1) (local.get $c1)))
        (local.set $acc2 (f32x4.mul (local.get $acc2) (local.get $c1)))
        (local.set $acc3 (f32x4.mul (local.get $acc3) (local.get $c1)))

        ;; 4 vector additions (16 scalar adds)
        (local.set $acc0 (f32x4.add (local.get $acc0) (local.get $c2)))
        (local.set $acc1 (f32x4.add (local.get $acc1) (local.get $c2)))
        (local.set $acc2 (f32x4.add (local.get $acc2) (local.get $c2)))
        (local.set $acc3 (f32x4.add (local.get $acc3) (local.get $c2)))

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $continue)
      )
    )

    ;; Return sum of accumulators as checksum
    (f32x4.add
      (f32x4.add (local.get $acc0) (local.get $acc1))
      (f32x4.add (local.get $acc2) (local.get $acc3))
    )
  )

  ;; ============================================================
  ;; SIMD F64X2 BENCHMARK (Vectorized)
  ;; Performs N iterations of 8 vector operations each (4 mul + 4 add)
  ;; Each vector op processes 2 doubles simultaneously
  ;; Total FLOPs = N * 8 * 2 = N * 16
  ;; ============================================================
  (func (export "bench_f64x2_simd") (param $iterations i32) (result v128)
    (local $i i32)
    (local $acc0 v128)
    (local $acc1 v128)
    (local $acc2 v128)
    (local $acc3 v128)
    (local $c1 v128)
    (local $c2 v128)

    ;; Initialize accumulators
    (local.set $acc0 (v128.const f64x2 1.0 1.1))
    (local.set $acc1 (v128.const f64x2 1.2 1.3))
    (local.set $acc2 (v128.const f64x2 1.4 1.5))
    (local.set $acc3 (v128.const f64x2 1.6 1.7))

    ;; Constants for operations
    (local.set $c1 (v128.const f64x2 1.00000000001 1.00000000001))
    (local.set $c2 (v128.const f64x2 0.99999999999 0.99999999999))

    ;; Main loop
    (local.set $i (i32.const 0))
    (block $break
      (loop $continue
        (br_if $break (i32.ge_u (local.get $i) (local.get $iterations)))

        ;; 4 vector multiplications (8 scalar muls)
        (local.set $acc0 (f64x2.mul (local.get $acc0) (local.get $c1)))
        (local.set $acc1 (f64x2.mul (local.get $acc1) (local.get $c1)))
        (local.set $acc2 (f64x2.mul (local.get $acc2) (local.get $c1)))
        (local.set $acc3 (f64x2.mul (local.get $acc3) (local.get $c1)))

        ;; 4 vector additions (8 scalar adds)
        (local.set $acc0 (f64x2.add (local.get $acc0) (local.get $c2)))
        (local.set $acc1 (f64x2.add (local.get $acc1) (local.get $c2)))
        (local.set $acc2 (f64x2.add (local.get $acc2) (local.get $c2)))
        (local.set $acc3 (f64x2.add (local.get $acc3) (local.get $c2)))

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $continue)
      )
    )

    ;; Return sum of accumulators as checksum
    (f64x2.add
      (f64x2.add (local.get $acc0) (local.get $acc1))
      (f64x2.add (local.get $acc2) (local.get $acc3))
    )
  )

  ;; ============================================================
  ;; INTENSIVE SIMD BENCHMARK (Maximum throughput)
  ;; 16 vector operations per iteration for maximum parallelism
  ;; Total FLOPs per iteration = 16 * 4 = 64 (for f32x4)
  ;; ============================================================
  (func (export "bench_f32x4_intensive") (param $iterations i32) (result v128)
    (local $i i32)
    (local $v0 v128) (local $v1 v128) (local $v2 v128) (local $v3 v128)
    (local $v4 v128) (local $v5 v128) (local $v6 v128) (local $v7 v128)
    (local $c1 v128) (local $c2 v128)

    ;; Initialize vectors
    (local.set $v0 (v128.const f32x4 1.0 1.0 1.0 1.0))
    (local.set $v1 (v128.const f32x4 1.1 1.1 1.1 1.1))
    (local.set $v2 (v128.const f32x4 1.2 1.2 1.2 1.2))
    (local.set $v3 (v128.const f32x4 1.3 1.3 1.3 1.3))
    (local.set $v4 (v128.const f32x4 1.4 1.4 1.4 1.4))
    (local.set $v5 (v128.const f32x4 1.5 1.5 1.5 1.5))
    (local.set $v6 (v128.const f32x4 1.6 1.6 1.6 1.6))
    (local.set $v7 (v128.const f32x4 1.7 1.7 1.7 1.7))

    (local.set $c1 (v128.const f32x4 1.0000001 1.0000001 1.0000001 1.0000001))
    (local.set $c2 (v128.const f32x4 0.9999999 0.9999999 0.9999999 0.9999999))

    (local.set $i (i32.const 0))
    (block $break
      (loop $continue
        (br_if $break (i32.ge_u (local.get $i) (local.get $iterations)))

        ;; 8 multiplications
        (local.set $v0 (f32x4.mul (local.get $v0) (local.get $c1)))
        (local.set $v1 (f32x4.mul (local.get $v1) (local.get $c1)))
        (local.set $v2 (f32x4.mul (local.get $v2) (local.get $c1)))
        (local.set $v3 (f32x4.mul (local.get $v3) (local.get $c1)))
        (local.set $v4 (f32x4.mul (local.get $v4) (local.get $c1)))
        (local.set $v5 (f32x4.mul (local.get $v5) (local.get $c1)))
        (local.set $v6 (f32x4.mul (local.get $v6) (local.get $c1)))
        (local.set $v7 (f32x4.mul (local.get $v7) (local.get $c1)))

        ;; 8 additions
        (local.set $v0 (f32x4.add (local.get $v0) (local.get $c2)))
        (local.set $v1 (f32x4.add (local.get $v1) (local.get $c2)))
        (local.set $v2 (f32x4.add (local.get $v2) (local.get $c2)))
        (local.set $v3 (f32x4.add (local.get $v3) (local.get $c2)))
        (local.set $v4 (f32x4.add (local.get $v4) (local.get $c2)))
        (local.set $v5 (f32x4.add (local.get $v5) (local.get $c2)))
        (local.set $v6 (f32x4.add (local.get $v6) (local.get $c2)))
        (local.set $v7 (f32x4.add (local.get $v7) (local.get $c2)))

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $continue)
      )
    )

    ;; Reduce all vectors to single result
    (f32x4.add
      (f32x4.add
        (f32x4.add (local.get $v0) (local.get $v1))
        (f32x4.add (local.get $v2) (local.get $v3))
      )
      (f32x4.add
        (f32x4.add (local.get $v4) (local.get $v5))
        (f32x4.add (local.get $v6) (local.get $v7))
      )
    )
  )

  ;; ============================================================
  ;; MIXED OPERATIONS BENCHMARK
  ;; Tests mul, add, sub, and div operations
  ;; Total FLOPs = N * 16 (4 ops * 4 lanes)
  ;; ============================================================
  (func (export "bench_f32x4_mixed") (param $iterations i32) (result v128)
    (local $i i32)
    (local $acc v128)
    (local $c1 v128)
    (local $c2 v128)
    (local $c3 v128)
    (local $c4 v128)

    (local.set $acc (v128.const f32x4 100.0 100.0 100.0 100.0))
    (local.set $c1 (v128.const f32x4 1.01 1.01 1.01 1.01))
    (local.set $c2 (v128.const f32x4 0.5 0.5 0.5 0.5))
    (local.set $c3 (v128.const f32x4 0.25 0.25 0.25 0.25))
    (local.set $c4 (v128.const f32x4 1.001 1.001 1.001 1.001))

    (local.set $i (i32.const 0))
    (block $break
      (loop $continue
        (br_if $break (i32.ge_u (local.get $i) (local.get $iterations)))

        ;; mul
        (local.set $acc (f32x4.mul (local.get $acc) (local.get $c1)))
        ;; add
        (local.set $acc (f32x4.add (local.get $acc) (local.get $c2)))
        ;; sub
        (local.set $acc (f32x4.sub (local.get $acc) (local.get $c3)))
        ;; div
        (local.set $acc (f32x4.div (local.get $acc) (local.get $c4)))

        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $continue)
      )
    )

    (local.get $acc)
  )
)

;; ============================================================
;; TEST ASSERTIONS
;; These verify the benchmarks execute correctly with 0 iterations (base case)
;; ============================================================

;; Test scalar f32 benchmark (0 iterations) - returns sum of initial accumulators
;; acc0=1.0 + acc1=1.1 + acc2=1.2 + acc3=1.3 = 4.6
(assert_return (invoke "bench_f32_scalar" (i32.const 0)) (f32.const 4.6))

;; Test scalar f64 benchmark (0 iterations)
(assert_return (invoke "bench_f64_scalar" (i32.const 0)) (f64.const 4.6))

;; ============================================================
;; FLOPS CALCULATION REFERENCE
;; ============================================================
;;
;; To calculate FLOPS from simulation:
;;
;; bench_f32_scalar:    FLOPs = iterations * 8
;; bench_f64_scalar:    FLOPs = iterations * 8
;; bench_f32x4_simd:    FLOPs = iterations * 32  (8 ops * 4 lanes)
;; bench_f64x2_simd:    FLOPs = iterations * 16  (8 ops * 2 lanes)
;; bench_f32x4_intensive: FLOPs = iterations * 64 (16 ops * 4 lanes)
;; bench_f32x4_mixed:   FLOPs = iterations * 16  (4 ops * 4 lanes)
;;
;; FLOPS = Total_FLOPs / (cycles * clock_period)
;;
;; Example at 100MHz (10ns period):
;;   1000 iterations of bench_f32x4_intensive = 64,000 FLOPs
;;   If completed in 50,000 cycles at 100MHz (500us):
;;   FLOPS = 64,000 / 0.0005 = 128 MFLOPS
;;
