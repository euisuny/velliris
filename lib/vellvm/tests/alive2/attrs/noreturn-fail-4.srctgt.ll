declare void @f()

define i8 @src() {
  call void @f()
  ret i8 0
}

define i8 @tgt() {
  call void @f() noreturn
  ret i8 0
}

; ERROR: Source and target don't have the same return domain

; Assertions below this point were automatically generated

; ASSERT SRCTGT 100
