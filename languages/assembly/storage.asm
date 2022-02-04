;; different ways of storing & accessing data - variables or registers or raw data

;; registers act as immediately accessible memory - they're built into the processor itself
;; whilst they're quicker to access, there's not many, so we store in main memory other bits of data not immediately needed
;; registers are divided into small subsections of the register - each register has an ah, al (capable of storing 8 bits in each), together making ax (16 bits), which makes the lower half eax (32 bits) which makes the lower half of the full rax (64 bits)
;; also raw data (ie '3', 0 in code) can only be stored directly in a register w/o size concerns

;; main memory store aka variables are accesible via pointer mechanisms
;; declaring a variable either involves declaration&initialisation (using d* commands (e.g. db, dw, etc.) or just initialisation (using res* commands (e.g. resb, resw, etc.)
;; you can declare as many variables wherever you like (remember, storing variables in .data or .bss results in them being global variables, whilst variables declared in functions (labels jumped to via call instruction) will be deallocated and removed from the stack when they are run)
;; you can create lists by simply defining multiple segments of memory on one line using the TIMES directive (ie define a word 9 times)
;; accessing it's data is done via dereferencing using [] (ie [var])
;; [] dereferences any given memory address, such that you access the byte after a pointer's start by writing [var + 1] (especially useful accessing nth elements in lists)
;; raw data (ie '3', 0 in code) can only be stored directly when size of variable is mentioned - so assembler knows how long to write for

;; you can set registers from values in main memory and vice versa

;; remember, storing variables in .data or .bss results in them being global variables

section .data
	SYS_EXIT equ 1 ;; define constant, map to 1 
	SYS_WRITE equ 4 ;;
	STD_OUT equ 1 ;;
	marks  TIMES  9  DW  0 ;; create an array called marks containing of 9 words, initialise to 0
	
section .bss
	num resb 1 ;; reserve a byte
	list2  TIMES  9  resb 1 ;; reserve an array of 9 words, called list2
	
section .text
	global _start
	
_start:
	mov ecx, '3' ;; note, you cannot copy raw data into RAM w/o register inbetween or size of data being stored
	mov [num], ecx ;; dereference memory, copy from register. accessing data from register requires no extra steps (no [], straight to value within)

	;; OR
	
	mov byte [num], '3' ;; dereference memory, copy from register. accessing data from register requires no extra steps (no [], straight to value within)

	mov eax, SYS_WRITE
	mov ebx, STD_OUT
	mov ecx, num ;; remember, sys_write requires a pointer to a buffer to read from, not data itself
	mov edx, 1
	int 0x80 ;; interrupt

	mov eax, SYS_EXIT
	mov ebx, 0
	int 0x80
