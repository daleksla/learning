name ?= bob

target:
	nasm -f elf64 -g $(name).asm -o $(name).o
	ld -d -m elf_x86_64 -o $(name) $(name).o
	rm $(name).o
