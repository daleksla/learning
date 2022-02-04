;; strings = series of characters stored contiguously in memory
;; the "$-" operator, placed in from of the string name, can identify length of a given string / variable
;; strings should be properly terminated by a sentinel character (eg 0, 0b, 0x0, 0h) 
;; ASM has instructions to handle strings, however there are pre-requirements:
	;; you must specify the direction before operation for how to copy / compare by setting the 'direction flag' - use CLD command to make operation left->right, from right->left use STD command
	;; you must set the length of the string in ecx
	;; you actually specify the string instruction as an operand - before that, you must specify how long it should continue comparing / copying memory amounts for. these commands follow the REP* pattern
		;; REP - repeat till counter is 0
		;; REPE/REPZ - repeat while zero flag (arithmetic returns) equals 0 or counter has not reached zero
		;; REPNE/REPNZ - repeat while zero flag (arithmetic returns) does not equals 0 or counter has not reached zero
;; ASM instructions to handle strings are to move and compare, with different instruction based on locality:
	;; moving (well, copying) strings: from memory-memory: MOVS, memory-register: LODS, register-memory: STOS
	;; comparing strings: two strings in memory: CMPS, memory-register: SCAS
	;; all these commands end in B(yte), W(ord), D(oubleword), depending on how much you want to be moved at a time (e.g. MOSB)
	;; note: strings in registers must be in either in AL, AX, EAX / RAX
	;; note: for LODS command grouo, if operand is one byte, put in AL register. if it's one word, put in AX register, and if it's a doubleword, put in EAX register (and I suppose quadwords go in the RAX register)

section .data
	s1 db 'Hello world!', 0 ;; string 1
	len equ $-s1

section .bss
	s2 resb 20 ;; destination

section .text
	global _start
	
_start:
	mov rcx, len ;; length of string to copy
	mov rsi, s1  ;; put pointer of string to copy
	mov rdi, s2  ;; pointer to string to paste in
	cld ;; specify direction
	rep movsb ;; keep moving byte-by-byte from string in src register to dest register till ecx counter goes to 0

	mov eax, 4 ;; system call number (sys_write)
	mov ebx, 1 ;; file descriptor (stdout)
	mov ecx, s2 ;; message to write
	mov edx, len ;; message length
	int 0x80 ;; call kernel
	
	mov eax, 1 ;; system call number (sys_exit)
	mov ebx, 0 ;; exit code 0
	int 0x80 ;; call kernel
