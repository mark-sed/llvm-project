; RUN: opt -verify-loop-info -irce-skip-profitability-checks -irce-print-changed-loops -passes=irce -disable-output < %s 2>&1 | FileCheck %s --implicit-check-not=constrained
; RUN: opt -verify-loop-info -irce-skip-profitability-checks -irce-print-changed-loops -passes=irce -disable-output -scalar-evolution-max-dom-tree-guard-steps=2 < %s 2>&1 | FileCheck %s --check-prefix=TWO-STEPS --implicit-check-not=constrained
; RUN: opt -verify-loop-info -irce-skip-profitability-checks -irce-print-changed-loops -passes=irce -disable-output -scalar-evolution-max-dom-tree-guard-steps=0 < %s 2>&1 | FileCheck %s --check-prefix=NO-STEPS --implicit-check-not=constrained

; Sibling loops share the trip count %size. Each loop has an eq latch
; (++i == %size), which IRCE can only handle if %size is known to be non-zero on
; entry. Constraining a loop splits it into a main loop and a post-loop that
; both exit to the next sibling's preheader, turning that preheader into a join.
; SCEV must find the guard dominating the join to prove %size != 0 there.
;
; Each constrained sibling in front of a loop costs two dominator tree steps, so
; a budget of two steps covers the second loop but not the third. With no steps
; SCEV leaves the outer loop at the join, as before; the third loop in
; @three_siblings is still constrained then, because the second one is not split.

; CHECK: irce: in function two_siblings: constrained Loop at depth 2 containing: %a<header>
; CHECK: irce: in function two_siblings: constrained Loop at depth 2 containing: %b<header>
; CHECK: irce: in function three_siblings: constrained Loop at depth 2 containing: %a<header>
; CHECK: irce: in function three_siblings: constrained Loop at depth 2 containing: %b<header>
; CHECK: irce: in function three_siblings: constrained Loop at depth 2 containing: %c<header>
; CHECK: irce: in function nested_siblings: constrained Loop at depth 3 containing: %a<header>
; CHECK: irce: in function nested_siblings: constrained Loop at depth 3 containing: %b<header>
; CHECK: irce: in function guard_not_dominating: constrained Loop at depth 2 containing: %a<header>

; TWO-STEPS: irce: in function two_siblings: constrained Loop at depth 2 containing: %a<header>
; TWO-STEPS: irce: in function two_siblings: constrained Loop at depth 2 containing: %b<header>
; TWO-STEPS: irce: in function three_siblings: constrained Loop at depth 2 containing: %a<header>
; TWO-STEPS: irce: in function three_siblings: constrained Loop at depth 2 containing: %b<header>
; TWO-STEPS: irce: in function nested_siblings: constrained Loop at depth 3 containing: %a<header>
; TWO-STEPS: irce: in function nested_siblings: constrained Loop at depth 3 containing: %b<header>
; TWO-STEPS: irce: in function guard_not_dominating: constrained Loop at depth 2 containing: %a<header>

; NO-STEPS: irce: in function two_siblings: constrained Loop at depth 2 containing: %a<header>
; NO-STEPS: irce: in function three_siblings: constrained Loop at depth 2 containing: %a<header>
; NO-STEPS: irce: in function three_siblings: constrained Loop at depth 2 containing: %c<header>
; NO-STEPS: irce: in function nested_siblings: constrained Loop at depth 3 containing: %a<header>
; NO-STEPS: irce: in function guard_not_dominating: constrained Loop at depth 2 containing: %a<header>
; SCEV must find the guard dominating the join to prove %size != 0 there.

; Two siblings: both loops are constrained.
define void @two_siblings(ptr %arr, ptr %len.ptr, i32 %n, i32 %m, ptr %p) {
entry:
  %len = load i32, ptr %len.ptr, !range !0
  br label %outer

outer:
  %o = phi i32 [ 0, %entry ], [ %o.next, %outer.latch ]
  %size = phi i32 [ %n, %entry ], [ %size.next, %outer.latch ]
  %is.zero = icmp eq i32 %size, 0
  br i1 %is.zero, label %outer.latch, label %a.preheader

a.preheader:
  br label %a

a:
  %a.iv = phi i32 [ 0, %a.preheader ], [ %a.iv.next, %a.latch ]
  %a.in.size = icmp slt i32 %a.iv, %size
  br i1 %a.in.size, label %a.check, label %oob

a.check:
  %a.in.len = icmp ult i32 %a.iv, %len
  br i1 %a.in.len, label %a.latch, label %oob

a.latch:
  %a.gep = getelementptr inbounds i32, ptr %arr, i32 %a.iv
  store i32 0, ptr %a.gep
  %a.iv.next = add nuw nsw i32 %a.iv, 1
  %a.done = icmp eq i32 %a.iv.next, %size
  br i1 %a.done, label %b.preheader, label %a

b.preheader:
  br label %b

b:
  %b.iv = phi i32 [ 0, %b.preheader ], [ %b.iv.next, %b.latch ]
  %b.in.size = icmp slt i32 %b.iv, %size
  br i1 %b.in.size, label %b.check, label %oob

b.check:
  %b.in.len = icmp ult i32 %b.iv, %len
  br i1 %b.in.len, label %b.latch, label %oob

b.latch:
  %b.gep = getelementptr inbounds i32, ptr %arr, i32 %b.iv
  store i32 1, ptr %b.gep
  %b.iv.next = add nuw nsw i32 %b.iv, 1
  %b.done = icmp eq i32 %b.iv.next, %size
  br i1 %b.done, label %outer.latch.loopexit, label %b

outer.latch.loopexit:
  br label %outer.latch

outer.latch:
  %size.next = load i32, ptr %p
  %o.next = add nuw nsw i32 %o, 1
  %outer.cont = icmp slt i32 %o.next, %m
  br i1 %outer.cont, label %outer, label %exit

oob:
  ret void

exit:
  ret void
}

; Three siblings: constraining each loop creates a join in front of the next.
define void @three_siblings(ptr %arr, ptr %len.ptr, i32 %n, i32 %m, ptr %p) {
entry:
  %len = load i32, ptr %len.ptr, !range !0
  br label %outer

outer:
  %o = phi i32 [ 0, %entry ], [ %o.next, %outer.latch ]
  %size = phi i32 [ %n, %entry ], [ %size.next, %outer.latch ]
  %is.zero = icmp eq i32 %size, 0
  br i1 %is.zero, label %outer.latch, label %a.preheader

a.preheader:
  br label %a

a:
  %a.iv = phi i32 [ 0, %a.preheader ], [ %a.iv.next, %a.latch ]
  %a.in.size = icmp slt i32 %a.iv, %size
  br i1 %a.in.size, label %a.check, label %oob

a.check:
  %a.in.len = icmp ult i32 %a.iv, %len
  br i1 %a.in.len, label %a.latch, label %oob

a.latch:
  %a.gep = getelementptr inbounds i32, ptr %arr, i32 %a.iv
  store i32 0, ptr %a.gep
  %a.iv.next = add nuw nsw i32 %a.iv, 1
  %a.done = icmp eq i32 %a.iv.next, %size
  br i1 %a.done, label %b.preheader, label %a

b.preheader:
  br label %b

b:
  %b.iv = phi i32 [ 0, %b.preheader ], [ %b.iv.next, %b.latch ]
  %b.in.size = icmp slt i32 %b.iv, %size
  br i1 %b.in.size, label %b.check, label %oob

b.check:
  %b.in.len = icmp ult i32 %b.iv, %len
  br i1 %b.in.len, label %b.latch, label %oob

b.latch:
  %b.gep = getelementptr inbounds i32, ptr %arr, i32 %b.iv
  store i32 1, ptr %b.gep
  %b.iv.next = add nuw nsw i32 %b.iv, 1
  %b.done = icmp eq i32 %b.iv.next, %size
  br i1 %b.done, label %c.preheader, label %b

c.preheader:
  br label %c

c:
  %c.iv = phi i32 [ 0, %c.preheader ], [ %c.iv.next, %c.latch ]
  %c.in.size = icmp slt i32 %c.iv, %size
  br i1 %c.in.size, label %c.check, label %oob

c.check:
  %c.in.len = icmp ult i32 %c.iv, %len
  br i1 %c.in.len, label %c.latch, label %oob

c.latch:
  %c.gep = getelementptr inbounds i32, ptr %arr, i32 %c.iv
  store i32 2, ptr %c.gep
  %c.iv.next = add nuw nsw i32 %c.iv, 1
  %c.done = icmp eq i32 %c.iv.next, %size
  br i1 %c.done, label %outer.latch.loopexit, label %c

outer.latch.loopexit:
  br label %outer.latch

outer.latch:
  %size.next = load i32, ptr %p
  %o.next = add nuw nsw i32 %o, 1
  %outer.cont = icmp slt i32 %o.next, %m
  br i1 %outer.cont, label %outer, label %exit

oob:
  ret void

exit:
  ret void
}

; Siblings nested one level deeper, inside %middle; the guard is in %middle.
define void @nested_siblings(ptr %arr, ptr %len.ptr, i32 %n, i32 %m, ptr %p) {
entry:
  %len = load i32, ptr %len.ptr, !range !0
  br label %outer

outer:
  %o = phi i32 [ 0, %entry ], [ %o.next, %outer.latch ]
  %size = phi i32 [ %n, %entry ], [ %size.next, %outer.latch ]
  br label %middle

middle:
  %k = phi i32 [ 0, %outer ], [ %k.next, %middle.latch ]
  %is.zero = icmp eq i32 %size, 0
  br i1 %is.zero, label %middle.latch, label %a.preheader

a.preheader:
  br label %a

a:
  %a.iv = phi i32 [ 0, %a.preheader ], [ %a.iv.next, %a.latch ]
  %a.in.size = icmp slt i32 %a.iv, %size
  br i1 %a.in.size, label %a.check, label %oob

a.check:
  %a.in.len = icmp ult i32 %a.iv, %len
  br i1 %a.in.len, label %a.latch, label %oob

a.latch:
  %a.gep = getelementptr inbounds i32, ptr %arr, i32 %a.iv
  store i32 0, ptr %a.gep
  %a.iv.next = add nuw nsw i32 %a.iv, 1
  %a.done = icmp eq i32 %a.iv.next, %size
  br i1 %a.done, label %b.preheader, label %a

b.preheader:
  br label %b

b:
  %b.iv = phi i32 [ 0, %b.preheader ], [ %b.iv.next, %b.latch ]
  %b.in.size = icmp slt i32 %b.iv, %size
  br i1 %b.in.size, label %b.check, label %oob

b.check:
  %b.in.len = icmp ult i32 %b.iv, %len
  br i1 %b.in.len, label %b.latch, label %oob

b.latch:
  %b.gep = getelementptr inbounds i32, ptr %arr, i32 %b.iv
  store i32 1, ptr %b.gep
  %b.iv.next = add nuw nsw i32 %b.iv, 1
  %b.done = icmp eq i32 %b.iv.next, %size
  br i1 %b.done, label %middle.latch.loopexit, label %b

middle.latch.loopexit:
  br label %middle.latch

middle.latch:
  %k.next = add nuw nsw i32 %k, 1
  %middle.cont = icmp slt i32 %k.next, %m
  br i1 %middle.cont, label %middle, label %outer.latch

outer.latch:
  %size.next = load i32, ptr %p
  %o.next = add nuw nsw i32 %o, 1
  %outer.cont = icmp slt i32 %o.next, %m
  br i1 %outer.cont, label %outer, label %exit

oob:
  ret void

exit:
  ret void
}

; Negative test: the guard only covers the first loop. The second loop is also
; reachable with %size == 0 through %skip, so its eq latch must not be
; rewritten, and only the first loop is constrained.
define void @guard_not_dominating(ptr %arr, ptr %len.ptr, i32 %n, i32 %m, ptr %p) {
entry:
  %len = load i32, ptr %len.ptr, !range !0
  br label %outer

outer:
  %o = phi i32 [ 0, %entry ], [ %o.next, %outer.latch ]
  %size = phi i32 [ %n, %entry ], [ %size.next, %outer.latch ]
  %is.zero = icmp eq i32 %size, 0
  br i1 %is.zero, label %skip, label %a.preheader

skip:
  br label %b.preheader

a.preheader:
  br label %a

a:
  %a.iv = phi i32 [ 0, %a.preheader ], [ %a.iv.next, %a.latch ]
  %a.in.size = icmp slt i32 %a.iv, %size
  br i1 %a.in.size, label %a.check, label %oob

a.check:
  %a.in.len = icmp ult i32 %a.iv, %len
  br i1 %a.in.len, label %a.latch, label %oob

a.latch:
  %a.gep = getelementptr inbounds i32, ptr %arr, i32 %a.iv
  store i32 0, ptr %a.gep
  %a.iv.next = add nuw nsw i32 %a.iv, 1
  %a.done = icmp eq i32 %a.iv.next, %size
  br i1 %a.done, label %a.exit, label %a

a.exit:
  br label %b.preheader

b.preheader:
  br label %b

b:
  %b.iv = phi i32 [ 0, %b.preheader ], [ %b.iv.next, %b.latch ]
  %b.in.size = icmp slt i32 %b.iv, %size
  br i1 %b.in.size, label %b.check, label %oob

b.check:
  %b.in.len = icmp ult i32 %b.iv, %len
  br i1 %b.in.len, label %b.latch, label %oob

b.latch:
  %b.gep = getelementptr inbounds i32, ptr %arr, i32 %b.iv
  store i32 1, ptr %b.gep
  %b.iv.next = add nuw nsw i32 %b.iv, 1
  %b.done = icmp eq i32 %b.iv.next, %size
  br i1 %b.done, label %outer.latch.loopexit, label %b

outer.latch.loopexit:
  br label %outer.latch

outer.latch:
  %size.next = load i32, ptr %p
  %o.next = add nuw nsw i32 %o, 1
  %outer.cont = icmp slt i32 %o.next, %m
  br i1 %outer.cont, label %outer, label %exit

oob:
  ret void

exit:
  ret void
}

!0 = !{i32 0, i32 2147483647}
;.
;.
