;; dynamic memory allocation in assembly involves changing the location of the program break, which defines the end of the process's data segment (ie end of .data & .bss sections)
;; Increasing the program break has the effect of allocating memory to the process
;; decreasing the break deallocates memory (important to prevent memory leaks - the heap space is finite, and if you keep asking for memory, the program break eventually cannot move anymore - moving back the program break after you're done with it ensures memory is availabl-e to be asked for later) 
;; we use the sys_brk syscall to determine where and moving the program break

section .text
	global _start	

_exit:
	mov rax, 60 ;; sys_exit
	mov rdi, 0 ;; exit code 0
	syscall

_malloc:
	push ebp
	mov ebp, esp

	mov rdx, 

	mov rax, 12 ;; sys_brk
	mov rdi, 0 ;; get current endpoint of heap, so pass 0
	syscall ;; result will be stored in rax
	
	mov rbx, rax ;; copy address of end-point pointer - we're allocating after it
	
	lea rdi, [rax+4] ;; store as an argument to sys_brk by placing in register as arg
	mov rax, 12 ;; call sys_brk again
	syscall ;; interrupt	

	mov esp, ebp
	pop ebp
	
_start:

	mov dword [rbx], 'sali'
	
	mov rax, 1
	mov rdi, 1
	mov rsi, rbx ;; copy address of allocated memory
	mov rdx, 4
	syscall
	
	jmp _exit
