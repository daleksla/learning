;; this file will cover to write & call functions in assembly
;; they're similar to goto's in that they're a label which you jump to
;; however, functions must be called use CALL instruction, and must have a RET(urn) command at the end (handily returns to calling line without the need of another goto or to be placed in a proper location) - this is because CALL implicitly pushes the return address on the stack, which is then accessed by RET command by going for the last pushed thing to the stack
;; manipulating the stack for other purposes involves manipulation the SS and ESP/RSP register, directly or indirectly via the POP & PUSH commands (the latter two are esp useful when you need to quickly swap out information from a register for quick use elsewhere (such as printing variables in a for loop where ecx is counter variable))
	;; ***REMEMBER: THE STACK GOES FROM HIGH ADDRESS' TO LOW ADDRESS' (eg push 5 @ 0x12, push 6 @ 0x11)
;; with functions in other languages, it's important to have seperate stack frame, such that variables created within a function are deleted afterwards
;; to pass arguments, you must push the arguments onto the stack, right arg to left (e.g C's foo(a,b,c) -> ASM's push c, push b, push a, call foo)
;; then, in the function itself, save the old stackBASE pointer on the stack and set as the value of our current stack-pointer (which points to last byte on the stack) - this way we set a stackframe which can be deleted when we're done with it and so we don't intrude on memory of calling function
;; to access arguments, using the new stackbase pointer, simply access it like a pointer
	;; since variables were pushed before stackframe was set up (and therefore have a higher address than our current stackbase pointer***), we go x + 4 + y to access our first argument (where x is base pointer, 4 is the size of the return address, y is the amount of bytes our parameter takes up). then dereference from that point the amount of space you needed
;; to reserve space for local variables, simply shift the STACK pointer (the one which points to last byte on stack) by however much you want (remember, you would shrink the stack pointer by however many bytes you wish to reserve)
;; at the end of the function, we restore the stackpointer to the stackbase pointer (so it points to basically the last thing pushed onto the stack from the caller function), then we reset the stackbase to the base of it's caller (by popping the old value off the stack)
;; inline functions are for another day, but essentially it would just plop the contents of aforementioned inline function where you would otherwise call it

section .data
	txt dw '25'

section .text
	global _start

_exit:
	mov rax, 60
	mov rdi, 0
	syscall

_print_arg:
	;; function_initialisation
	push rbp ;; save old stackbase value
	mov rbp, rsp ;; set new stack base from tail of last value added to stack
	
	;; actual function
	mov rax, 1
	mov rdi, 1
	lea rsi, [rbp + 8 + 8] ;; access stackbase, skip old base pointer, skip return address (8 bytes long)
	mov rdx, 2 ;; read two bytes from said point
	syscall
	
	;; function_finalisation
	mov rsp, rbp ;; set stack pointer as this frames stack base (ie set ebp to tail of old function)
	pop rbp ;; set stack base pointer as original base of caller
	ret ;; return to last value stored on stack, which at this point is the implicitly pushed return address

_start:
	push word [txt] ;; push only arg to stack, word
	call _print_arg ;; implicitly push return address, call function
	pop rax ;; just a way to pop old value off the stack
	jmp _exit ;; exit routine, just a goto
