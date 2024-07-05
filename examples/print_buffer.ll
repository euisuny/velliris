; ModuleID = 'print_buffer.c'
source_filename = "print_buffer.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

; Function Attrs: noinline nounwind optnone uwtable
define void @print_buffer(i8** %0, i64 %1) #0 {
  %3 = alloca i8**, align 8
  %4 = alloca i64, align 8
  %5 = alloca i64, align 8
  store i8** %0, i8*** %3, align 8
  store i64 %1, i64* %4, align 8
  store i64 0, i64* %5, align 8
  br label %6

6:                                                ; preds = %13, %2
  %7 = load i8**, i8*** %3, align 8
  %8 = load i64, i64* %5, align 8
  %9 = getelementptr inbounds i8*, i8** %7, i64 %8
  %10 = load i8*, i8** %9, align 8
  call void @print_string(i8* %10)
  %11 = load i64, i64* %5, align 8
  %12 = add i64 %11, 1
  store i64 %12, i64* %5, align 8
  br label %13

13:                                               ; preds = %6
  %14 = load i64, i64* %5, align 8
  %15 = load i64, i64* %4, align 8
  %16 = icmp ne i64 %14, %15
  br i1 %16, label %6, label %17

17:                                               ; preds = %13
  ret void
}

declare void @print_string(i8*) #1

attributes #0 = { noinline nounwind optnone uwtable "disable-tail-calls"="true" "frame-pointer"="non-leaf" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+neon,+outline-atomics,+v8a" }
attributes #1 = { "frame-pointer"="non-leaf" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+neon,+outline-atomics,+v8a" }

!llvm.module.flags = !{!0, !1, !2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 1, !"branch-target-enforcement", i32 0}
!2 = !{i32 1, !"sign-return-address", i32 0}
!3 = !{i32 1, !"sign-return-address-all", i32 0}
!4 = !{i32 1, !"sign-return-address-with-bkey", i32 0}
!5 = !{i32 7, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 7, !"uwtable", i32 1}
!8 = !{i32 7, !"frame-pointer", i32 1}
!9 = !{!"Ubuntu clang version 14.0.6"}
!11 = !{!"llvm.loop.mustprogress"}
