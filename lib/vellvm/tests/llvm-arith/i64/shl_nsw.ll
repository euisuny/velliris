define i64 @main(i64 %argc, i8** %arcv) {
  %1 = shl nsw i64 4611686018427387904, 5
  ret i64 %1
}
; ASSERT POISON: call i1 @main(i64 1, i8** null)
