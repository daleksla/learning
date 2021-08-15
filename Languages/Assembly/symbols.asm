;; three different way to define const symbols
;; equ defines consts only
;; %assign defines numeric variable
;; %define defines both str & nums

section .data
	SYS_EXIT equ 1 ;; define constant, map to 1 
	%assign SYS_WRITE 4 ;;
	%assign STD_OUT 1 ;;
	%define NAME "SALIH"
	
	name db NAME ;; define name
	%assign len_name $-name 
	
section .text
	global _start
	
_start:
	mov eax, SYS_WRITE
	mov ebx, STD_OUT
	mov ecx, name ;; actual variable
	mov edx, len_name
	int 0x80

	mov eax, SYS_EXIT
	mov ebx, 0
	int 0x80
