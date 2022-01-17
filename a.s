	.data
	.globl	x
x:
	.zero	4
	.text
	.text
    .globl  main
    .type   main, @function
main:
    pushq   %rbp
    movq	%rsp, %rbp
    subq    $48, %rsp
	leaq	-12(%rbp), %r15
	movq	%r15, -36(%rbp)
	movq	$1, %r14
	movl	%r14d, -12(%rbp)
	movq	$2, %r13
	movl	%r13d, -16(%rbp)
	movq	$3, %r12
	movl	%r12d, -20(%rbp)
	movq	$6, %r11
	movl	%r11d, x(%rip)
	movq	$7, %r10
	movq	%r10, -28(%rbp)
	movq	$8, %r9
	movq	%r9, -28(%rbp)
	movq	$9, %r15
	leaq	-8(%rbp), %r8
	movq	$4, %r13
	movq	$0, %r14
	imulq	%r13, %r14
	subq	%r14, %r8
	movl	%r15d, (%r8)
	movl	x(%rip), %r10d
	leaq	-8(%rbp), %r11
	movq	$4, %r13
	movq	$0, %r9
	imulq	%r13, %r9
	subq	%r9, %r11
	movl	(%r11), %r11d
	addl	%r10d, %r11d
	movq	-28(%rbp), %r12
	addq	%r11, %r12
	movq	%r12, %rax
	jmp	func_main_ret
func_main_ret:
	addq	$48, %rsp
    popq	%rbp
    ret

