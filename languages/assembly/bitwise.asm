;; bitwise operations: AND, OR, NOT, XOR - comparing the bits of the respective operands
 
;; bitwise ops can also be used for masking, whereby you bitwise with a given set of numbers to select bits, enable or unset bits, allowing you to create new values with desired properties
	;; using AND and bitwising with a value preserves the bits you set as 1, nulls what you set as 0
	;; using OR and bitwising with a value enables the bits you set as 1, preserves the rest
	;; using XOR and bitwising with a value reverses the bits you set as 1, preserves the rest
	;; NOT simply inverts each bit in a sequence (0->1, 1->0)
	;; (some real world usages are mentioned at the bottom of this file)
	
;; the calculated bitwise'd value is stored in the first operand 
;; Note: the first operand in all the cases could be either in register or in memory, the second operand could be either in register/memory or an immediate (constant) value, but that memory-to-memory operations are not possible

;; note: there are flags which are set based on these computations and others
	;; these are used in conditional statements etc
	;; using such return values set in the flags will be covered seperately with other commands too

section .data
	%define SYS_WRITE 4
	%define STDOUT 1
	%define SYS_EXIT 1
	
section .bss
	result resw 1

section .text
	global _start
	
_start:
	mov byte [result], 'a'
	and byte [result], 11011111b ;; converting to upper case involves clearing bit 6
                                     ;; therefore we create a value to preserve all bits except bit 6
	;; byte variable now stores 'A'
	
	mov dl, 6 ;; single digit numerical value
	or dl, 0110000b ;; enable certain bits to add value and convert to ASCII equivalent
			;; now prints '6' - printable format

	;; exit
	mov eax, SYS_EXIT
	mov ebx, 0
	int 0x80
	
_print:
	mov eax, SYS_WRITE
	mov ebx, STDOUT
	mov ecx, result
	mov edx, 1
	int 0x80
	ret
	
;; 1. You will have situations where you need to set/clear/toggle just one single bit of a specific register without modifying the other contents. So, you will do a read and do an OR/AND/XOR operation with the appropriate mask for the bit position and write this new value to the register.
	
;; 2. Usually bitwise operations are faster than doing multiply/divide. So if you need to multiply a variable x by say 9, you will do (x<<3 + x) which would be a few cycles faster than (x*9). If this code is inside an ISR, you will save on response time.
	
;; 3. Similarly if you want to use an array as a circular queue, it'd be faster(and more elegant) to handle wrap around checks with bit wise operations. (your array size should be a power of 2). Eg: , you can use tail = ((tail & MASK )+ 1) instead of tail = ((tail +1) < size)?tail+1:0, if you want to insert/delete.
	
;; 4. Also if you want a error flag to hold multiple error codes together, each bit can hold a separate value. You can AND it with each individual error code as a check. This is used in Unix error codes.
	
;; 5. For signed values which use a bit as a signed value, you could simply AND it, negate the signed bit, and simply compare the magnitude of positive and negative data alike
