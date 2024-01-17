let primitives =
  ".len:
  xorq %rax, %rax
  jmp .loop_len
.loop_len:
  movb 0(%rdi, %rax), %bl
  cmpb $0, %bl
  je .len_ret
  incq %rax
  jmp .loop_len
.len_ret:
  ret
.mod16:
  pushq %rax
  pushq %rdx
  movq %rsp, %rax
  subq $24, %rax
  movq $16, %r8
  xorq %rdx, %rdx
  idivq %r8
  movq %rdx, %r8
  popq %rdx
  popq %rax
  ret
log:
  movq 8(%rsp), %rsi
  movq $.fmt, %rdi
  movq $0, %rax
  call .mod16
  cmpq $8, %r8
  je .dec_log
  call printf
  ret
  .dec_log:
    subq $8, %rsp
    call printf
    addq $8, %rsp
    ret
not:
  movq 8(%rsp), %rax
  notb %al
  ret
lessThanOrEq:
  xorq %rax, %rax
  movq 16(%rsp), %rbx
  cmpq %rbx, 8(%rsp)
  setle %al
  ret
lessThan:
  xorq %rax, %rax
  movq 16(%rsp), %rbx
  cmpq %rbx, 8(%rsp)
  setl %al
  ret
greaterThanOrEq:
  xorq %rax, %rax
  movq 16(%rsp), %rbx
  cmpq %rbx, 8(%rsp)
  setge %al
  ret
greaterThan:
  xorq %rax, %rax
  movq 16(%rsp), %rbx
  cmpq %rbx, 8(%rsp)
  setg %al
  ret
negate:
  movq 8(%rsp), %rax
  negq %rax
  ret
add:
  movq 8(%rsp), %rax
  addq 16(%rsp), %rax
  ret
sub:
  movq 8(%rsp), %rax
  subq 16(%rsp), %rax
  ret
mul:
  movq 8(%rsp), %rax
  imulq 16(%rsp), %rax
  ret
div:
  cmpq $0, 16(%rsp)
  je .div_0
  movq 8(%rsp), %rax
  cqo
  idivq 16(%rsp)
  cmpq $0, %rdx
  jl .div_neg
  ret
  .div_0:
    xorq %rax, %rax
    ret
  .div_neg:
    movq 16(%rsp), %rdx
    cmpq $0, %rdx
    jl .div_neg_neg
    decq %rax
    ret
    .div_neg_neg:
      incq %rax
      ret
mod:
  cmpq $0, 16(%rsp)
  je .div_0
  movq 8(%rsp), %rax
  cqo
  idivq 16(%rsp)
  cmpq $0, %rdx
  jl .mod_neg
  movq %rdx, %rax
  ret
  .mod_neg:
    movq 16(%rsp), %rax
    cmpq $0, %rax
    jl .mod_neg_neg
    addq %rdx, %rax
    ret
    .mod_neg_neg:
      negq %rax
      addq %rdx, %rax
      ret
.aligned_malloc:
  call .mod16
  cmpq $8, %r8
  je .dec_malloc
  call malloc
  jmp .aligned_malloc_ret
  .dec_malloc:
    subq $8, %rsp
    call malloc
    addq $8, %rsp
    jmp .aligned_malloc_ret
  .aligned_malloc_ret:
    ret
append:
  movq 8(%rsp), %rdi
  call .len
  movq %rax, %rcx
  movq 16(%rsp), %rdi
  call .len
  addq %rcx, %rax
  addq $1, %rax
  movq %rax, %rdi
  call .aligned_malloc
  movq 8(%rsp), %rdi
  movq %rax, %rcx
  movq %rax, %rdx
  xorq %rax, %rax
  .loop_append_1:
    movb (%rdi, %rax), %bl
    cmpb $0, %bl
    je .med_append
    movb %bl, (%rcx, %rax)
    incq %rax
    jmp .loop_append_1
  .med_append:
    addq %rax, %rcx
    xorq %rax, %rax
    movq 16(%rsp), %rdi 
  .loop_append_2:
    movb (%rdi, %rax), %bl
    movb %bl, (%rcx, %rax)
    cmpb $0, %bl
    je .loop_ret
    incq %rax
    jmp .loop_append_2
  .loop_ret:
    movq %rdx, %rax
    ret
.cmp_str_loop:
  movb 0(%rbx), %cl
  cmpb 0(%rax), %cl
  jne .cmp_str_ret
  xorb %cl, %cl
  cmpb 0(%rax), %cl
  je .cmp_str_ret
  incq %rax
  incq %rbx
  jmp .cmp_str_loop
.cmp_str_ret:
  ret
pure:
  xorq %rax, %rax
  ret
unit:
  xorq %rax, %rax
  ret
show:
  movq 8(%rsp), %rax
  call .show_int
  ret
.show_int:
  movq $10, %r8
  pushq %rbp
  movq %rsp, %rbp
  cmpq $0, %rax
  je .show_int_0
  jg .show_int_pos
  negq %rax
  jmp .show_int_neg
  .show_int_0:
    movq $2, %rdi
    call .aligned_malloc
    movb $48, (%rax)
    movq %rax, %rbx
    incq %rbx
    jmp .show_int_ret
  .show_int_pos:
    xorq %rdx, %rdx
    cmpq $0, %rax
    je .show_int_pos_quit
    idivq %r8
    addb $48, %dl
    pushq %rdx
    jmp .show_int_pos
    .show_int_pos_quit:
      movq %rsp, %rdi
      subq %rsp, %rdi
      incq %rdi
      call .aligned_malloc
      movq %rax, %rbx
      .show_int_pos_copy:
        cmpq %rsp, %rbp
        je .show_int_ret
        popq %rcx
        movb %cl, (%rbx)
        incq %rbx
        jmp .show_int_pos_copy
  .show_int_neg:
    xorq %rdx, %rdx
    cmpq $0, %rax
    je .show_int_neg_quit
    idivq %r8
    addb $48, %dl
    pushq %rdx
    jmp .show_int_neg
    .show_int_neg_quit:
      movq %rsp, %rdi
      subq %rsp, %rdi
      incq %rdi
      incq %rdi 
      call .aligned_malloc
      movq %rax, %rbx
      movb $45, (%rbx)
      incq %rbx
      .show_int_neg_copy:
        cmpq %rsp, %rbp
        je .show_int_ret
        popq %rcx
        movb %cl, (%rbx)
        incq %rbx
        jmp .show_int_neg_copy
  .show_int_ret:
    movb $0, (%rbx)
    leave
    ret
.eq_int:
  movq 24(%rsp), %rax
  cmpq 16(%rsp), %rax
  je .eq_int_eq
  xorq %rax, %rax
  ret
  .eq_int_eq:
    movq $255, %rax
    ret
eq:
  call .eq_int
  ret
notEq:
  pushq 16(%rsp)
  pushq 16(%rsp)
  call eq
  notb %al
  addq $16, %rsp
  ret
"