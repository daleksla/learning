;; in asm, control structures (such as loops, functions, etc.) don't natively exist
;; we can use goto labels to essentially jump to different locations in our program, using the JMP command

section .data
	msg db 'h' ;; value will be popped off stack when function ends
	len equ $-msg
	
_start:
	jmp _exit ;; here, we just jump to code containing a set of instructions
	
_exit:
	mov eax, 1
	mov ebx, 0
	int 0x80 ;; call interrupt
	
section .text
	global _start	
