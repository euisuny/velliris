define i64 @main(i64 %argc, i8** %arcv) {
  %1 = add nsw i64 -9223372036854775807, -5
  ret i64 %1
}
; ASSERT POISON: call i1 @main(i64 1, i8** null)
