;; basic hello world program
;; "sys.asm" reflects the why of how this works (how syscalls work), 
;; program also shows using fixed variables

section .data ;; stores constants
	msg db "Hello World!", 0xA ;; create a variable called msg, use db (define byte) to define a char, and based off the strings length, it'll keep define as many as are needed (string literal)
	len equ $-msg ;; get length of string message
	;; NOTE: equ does not create an actual tangible number. acts more like a macro for the assembler

section .text ;; stores actual code
	global _start ;; this tells linker which label the programs' execution begins	

_start:
	;; commands in asm follow format: [label]   mnemonic   [operands]
	
	mov rax, 4 ;; put into register syscall id for output (sys_write)
	mov rbx, 1 ;; store in register file descriptor (stdout)
	mov rcx, msg ;; provide pointer to start of message into another register
	mov rdx, len ;; provide placeholder to message length, copy into a register
	
	int 0x80 ;; int = interrupt, 0x80 is the id of the kernel, which handles it . it'll deal with the data found in the registers
	
	;; exit program now
	mov eax, 1 ;; put system call number into register (sys_exit)
	int 0x80 ;; call interrupt again to be handled by kernel
