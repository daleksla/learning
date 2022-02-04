;; program using 3 syscalls - read, write, exit
;; also makes use of run-time variables (section.bss section)
;; more advanced than "hello_world.asm"

section .data ;; stores constants
	prompt db "Enter number: " ;; create string (remember, db allocates needed memory)
	len_prompt equ $-prompt ;; get length of prompt msg	
	response db "Your number: " ;; 
	len_response equ $-response ;; get length of response msg

section .bss ;; stores declared variables, which we can change
	;; check link below for trigger words for byte allocation
	;; resb allocates 1 * n bytes
	;; https://stackoverflow.com/questions/44860003/how-many-bytes-do-resb-resw-resd-resq-allocate-in-nasm
	num resb 5 ;; declare a variable called number

section .text ;; stores actual code
	global _start ;; this tells linker which label the programs' execution begins	

_start:
	;; print prompt
	
	mov eax, 4 ;; put sys_call id into EAX register (4 = sys_write) 
	mov ebx, 1 ;; in EBX -> arg#1 file descriptor (stdout)
	mov ecx, prompt ;;  in ECX -> arg#2 message
	mov edx, len_prompt ;; in EDX -> arg#3 message length
	int 0x80 ;; trigger interrupt
	
	;; read user input
	
	mov eax, 3 ;; put sys_call id into EAX register (3 = sys_read) 
	mov ebx, 2 ;; in EBX -> arg#1 file descriptor (stdin)
	mov ecx, num ;; in ECX -> arg#2 buffer variable
	mov edx, 5 ;; in EDX -> arg#3 space available to write to (ie 5 bytes)
	int 0x80 ;; trigger interrupt  
	
	;; output the number entered
	;; FIRST, print message
	
	mov eax, 4 ;; put sys_call id into EAX register (4 = sys_write) 
	mov ebx, 1 ;; in EBX -> arg#1 file descriptor (stdout)
	mov ecx, response ;;  in ECX -> arg#2 message
	mov edx, len_response ;; in EDX -> arg#3 message length
	int 0x80 ;; trigger interrupt 
	
	;; now the actual number
	
	mov eax, 4 ;; put sys_call id into EAX register (4 = sys_write) 
	mov ebx, 1 ;; in EBX -> arg#1 file descriptor (stdout)
	mov ecx, num ;;  in ECX -> arg#2 number
	mov edx, 5 ;; in EDX -> arg#3 num length
	int 0x80 ;; trigger interrupt 
	
	;; exit program now
	
	mov eax, 1 ;; put system call number into register (sys_exit)
	mov ebx, 0 ;; put system call number into register (sys_exit)
	int 0x80 ;; call interrupt again to be handled by kernel
