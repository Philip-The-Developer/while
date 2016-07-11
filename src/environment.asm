;===============================================================================
; Import/ Export
;===============================================================================
global sign_mask
global alloc_error
global alloc_error2
global index_error
global return_error
global input_number
global output_number
global input_float
global output_float
global input_character
global output_character
global buffer.current
global buffer.remaining
global buffer
global exit_program
global env_class_class
global env_label_class
global label_env_parent
global label_env_labels
global label_env_offsets
global label_env_type
global label_env_index
global label_env_name
global label_env_new
global type_int
global type_double
global type_char
global type_ref  
global type_array_int
global type_array_double
global type_array_char
global type_array_ref
global main

extern printf
extern scanf
extern malloc
extern main_code
;===============================================================================
; Macros and Defines
;===============================================================================

; Length of our input buffer
%define buffer_length 24

; The macro which reads from STDIN via SYSCALL
%macro  read 0
    mov QWORD [buffer.current], buffer
    mov rax, 0
    mov rdi, 0
    mov rsi, buffer
    mov rdx, buffer_length
    syscall
    mov QWORD [buffer.remaining], rax
%endmacro

; Increment our rsi register (=buffer.current) and decrent the remaining bytes
%macro inc_rsi 0
    ; Move forward in our buffer
    inc rsi
    dec QWORD [buffer.remaining]
%endmacro

; Debugging macro, outputs the current value of [rsi]
%macro debug_rsi 0
     ;push rax
     ;xor rax, rax
     ;mov al, BYTE [rsi]
     ;add rax, 100000000
     ;call output_number
     ;pop rax
%endmacro

; Debugging macro, outputs the current value of [rsi]
%macro debug_rbp 0
     mov [macro_save], rax
     xor rax, rax
     mov rax, rbp
     call output_number
     mov rax, [macro_save]
%endmacro

%macro debug_rsp 0
     mov [macro_save], rax
     xor rax, rax
     mov rax, rsp
     call output_number
     mov rax, [macro_save]
%endmacro

;Macro to generate labels
%macro create_label 3-*
  mov QWORD [%1], env_label_class
  mov QWORD [%1+8], %2
  mov QWORD [%1+16], %3
  ;allociate character array for name
    mov rdx, %0-3
    multipush rcx, rsi, rdi, r8, r9, r10, r11
    push rdx
    imul rdi, rdx, 8
    add rdi, 8
    call malloc
    test rax, rax
    jz alloc_error
    pop QWORD [rax]
    multipop rcx, rsi, rdi, r8, r9, r10, r11
  mov QWORD [%1+24], rax
  %assign i 0
  %rep %0-3
    mov QWORD[rax+8+8*i], %4
    %rotate 1
    %assign i i+1
  %endrep
%endmacro

; Macros to push and pop multiple registers on the stack
; You don't have to reverse the argument order for pop
; Taken from: http://www.nasm.us/doc/nasmdoc4.html
%macro multipush 1-*
    %rep %0
        push %1
        %rotate 1
    %endrep
%endmacro
%macro multipop 1-*
    %rep %0
        %rotate -1
        pop %1
    %endrep
%endmacro
; $ Added macros for double-precision floating-point cases 
%macro multifpush 1-*
    %rep %0
        movq rax, %1
        push rax
        %rotate 1
    %endrep
%endmacro
%macro multifpop 1-*
    %rep %0
        %rotate -1
        pop rdx
        movq %1, rdx
    %endrep
%endmacro


;===============================================================================
; Initialized data
;===============================================================================
section .data

    ; The error message to be shown when seeing invalid symbols on STDIN
    error_message:      db  "Error: Input contains invalid symbol: 'x'", 10
    .len:               equ $ - error_message

    ; The error message to be shown when trying to read from empty STDIN
    eof_error_message:  db  "Error: No more input to read from.", 10
    .len:               equ $ - eof_error_message

    ;The error message to be shown when no eof or linebreak follows a char in STDIN
    char_error_message: db "Error: Expects a linebreak or EOF after reading a character.",10
    .len:               equ $ - char_error_message

    ; $ The error message to be shown when array memory allocation failed
    alloc_error_message:db  "Error: Array memory allocation failed.", 10
    .len:               equ $ - alloc_error_message

    ; $ The error message to be shown when forcing memory allocation of array with negative length
    alloc_error2_message:db  "Error: Memory allocation of array with negative length not possible.", 10
    .len:               equ $ - alloc_error2_message

    ; $ The error message to be shown when array index out of bounds
    index_error_message:db  "Error: Array index out of bounds.", 10
    .len:               equ $ - index_error_message

    ; $ The error message to be shown when function call does not return
    return_error_message:db  "Error: Function call does not return.", 10
    .len:                equ $ - return_error_message

    ; Saves whether the input is at EOF
    input_eof:          db 0

    ; $ Mask for inverting sign bit of double-precision floating-point numbers.
    sign_mask:          dq -0.0

    ; $ Formats a null-terminated string to a floating-point number.
    float_formatin:     db "%f\n"
    ; $ Formats a floating-point number to a null-terminated string.
    float_formatout:    db "%g", 10, 0

    ; Formats a character input
    character_formatin: db "%c\n"
    ; Formats a character output
    character_formatout: db "%c"
    
    ; empty array
    empty_array: dq 0

    ;primitive types
    type_int: dq 0, 0
    type_double: dq 0, 0
    type_char: dq 0, 0
    type_ref: dq 0, 0
    
    type_array_int: dq 1, 0
    type_array_double: dq 1, 0
    type_array_char: dq 1, 0
    type_array_ref: dq 1, 0
    
    type_function_ref_type_ref: dq 0, 2, type_ref, type_ref

;===============================================================================
; Uninitialized data
;===============================================================================
section .bss

    ; Reserve some space for the input buffer
    buffer:     resb buffer_length
    ; The pointer to the current position in our buffer
    .current:   resb 8
    ; The remaining bytes in our buffer
    .remaining: resb 8

    ; Reserve some space for the input character puffer
    char_buffer: resb 4

    macro_save: resq 1

;===============================================================================
; Default Objects provided by environment
;===============================================================================

    env_class_class: resb 40
    env_label_class: resb 40
    label_env_parent: resb 32
    label_env_labels: resb 32
    label_env_offsets: resb 32
    label_env_type: resb 32
    label_env_index: resb 32
    label_env_name: resb 32
    label_env_funcLabels: resb 32
    label_env_funcMap: resb 32
    label_env_new: resb 32

;===============================================================================
; Environment code
;===============================================================================
section .text


main:

    ; Initialize the memory we need for input stuff
    mov QWORD [buffer.remaining], 0
    mov QWORD [buffer.current], buffer

    ; $ Prepare new stack frame
    push rbp
    mov rbp, rsp

    ;=================================;
    ; Start object initialization     ;
    ;=================================;

      ;label ------------------------------------
      create_label label_env_parent, type_ref, 0, 'e', 'n', 'v', ':', 'p', 'a', 'r', 'e', 'n', 't'
      create_label label_env_labels, type_array_ref, 1, 'e', 'n', 'v', ':', 'l', 'a', 'b', 'e', 'l', 's'
      create_label label_env_offsets, type_array_int, 2, 'e', 'n', 'v', ':', 'o', 'f', 'f', 's', 'e', 't', 's'
      create_label label_env_type, type_ref, 1, 'e', 'n', 'v', ':', 't', 'y', 'p', 'e'
      create_label label_env_index, type_int, 2, 'e', 'n', 'v', ':', 'i', 'n', 'd', 'e', 'x'
      create_label label_env_name, type_array_char, 3, 'e', 'n', 'v', ':', 'n', 'a', 'm', 'e'
      create_label label_env_funcLabels, type_array_ref, 4, 'e', 'n', 'v', ':', 'f', 'u', 'n', 'c', 'L', 'a', 'b', 'e', 'l', 's'
      create_label label_env_funcMap, type_array_ref, 5, 'e', 'n', 'v', ':', 'f', 'u', 'n', 'c', 'M', 'a', 'p'
      create_label label_env_new, type_function_ref_type_ref, 0, 'e', 'n', 'v', ':', 'n', 'e','w'
      
      
      ;class class--------------------------------
      mov QWORD [env_class_class], env_class_class
      ;allociate reference array
      mov rdx, 5
      multipush rcx, rsi, rdi, r8, r9, r10, r11
      push rdx
      imul rdi, rdx, 8
      add rdi, 8
      call malloc
      test rax, rax
      jz alloc_error
      pop QWORD [rax]
      multipop rcx, rsi, rdi, r8, r9, r10, r11
      mov QWORD [env_class_class+8], rax
      mov QWORD [rax+8], label_env_parent
      mov QWORD [rax+16],label_env_labels
      mov QWORD [rax+24], label_env_offsets
      mov QWORD [rax+32], label_env_funcLabels
      mov QWORD [rax+40], label_env_funcMap
      
      ;allociate offset array
      mov rdx, 5
      multipush rcx, rsi, rdi, r8, r9, r10, r11
      push rdx
      imul rdi, rdx, 8
      add rdi, 8
      call malloc
      test rax, rax
      jz alloc_error
      pop QWORD [rax]
      multipop rcx, rsi, rdi, r8, r9, r10, r11
      mov QWORD [env_class_class+16], rax
      mov QWORD [rax+8], 0
      mov QWORD [rax+16], 8
      mov QWORD [rax+24], 16
      mov QWORD [rax+32], 24
      mov QWORD [rax+40], 32

      ;allociate function reference array
      mov rdx, 1
      multipush rcx, rsi, rdi, r8, r9, r10, r11
      push rdx
      imul rdi, rdx, 8
      add rdi, 8
      call malloc
      test rax, rax
      jz alloc_error
      pop QWORD [rax]
      multipop rcx, rsi, rdi, r8, r9, r10, r11
      mov QWORD [env_class_class+24], rax
      mov QWORD [rax+8], label_env_new
      
      ;allociate function offset array
      mov rdx, 1
      multipush rcx, rsi, rdi, r8, r9, r10, r11
      push rdx
      imul rdi, rdx, 8
      add rdi, 8
      call malloc
      test rax, rax
      jz alloc_error
      pop QWORD [rax]
      multipop rcx, rsi, rdi, r8, r9, r10, r11
      mov QWORD [env_class_class+32], rax
      mov QWORD [rax+8], new_

      ;label class--------------------------------
      mov QWORD [env_label_class], env_class_class
      ;allociate reference array
      mov rdx, 4
      multipush rcx, rsi, rdi, r8, r9, r10, r11
      push rdx
      imul rdi, rdx, 8
      add rdi, 8
      call malloc
      test rax, rax
      jz alloc_error
      pop QWORD [rax]
      multipop rcx, rsi, rdi, r8, r9, r10, r11
      mov QWORD [env_label_class+8], rax
      mov QWORD [rax+8], label_env_parent
      mov QWORD [rax+16],label_env_type
      mov QWORD [rax+24], label_env_index
      mov QWORD [rax+32], label_env_name
      
      ;allociate offset array
      mov rdx, 4
      multipush rcx, rsi, rdi, r8, r9, r10, r11
      push rdx
      imul rdi, rdx, 8
      add rdi, 8
      call malloc
      test rax, rax
      jz alloc_error
      pop QWORD [rax]
      multipop rcx, rsi, rdi, r8, r9, r10, r11
      mov QWORD [env_label_class+16], rax
      mov QWORD [rax+8], 0
      mov QWORD [rax+16], 8
      mov QWORD [rax+24], 16
      mov QWORD [rax+32], 24

      ;allociate function reference array
      mov rdx, 1
      multipush rcx, rsi, rdi, r8, r9, r10, r11
      push rdx
      imul rdi, rdx, 8
      add rdi, 8
      call malloc
      test rax, rax
      jz alloc_error
      pop QWORD [rax]
      multipop rcx, rsi, rdi, r8, r9, r10, r11
      mov QWORD [env_label_class+24], rax
      mov QWORD [rax+8], label_env_new
      
      ;allociate function offset array
      mov rdx, 1
      multipush rcx, rsi, rdi, r8, r9, r10, r11
      push rdx
      imul rdi, rdx, 8
      add rdi, 8
      call malloc
      test rax, rax
      jz alloc_error
      pop QWORD [rax]
      multipop rcx, rsi, rdi, r8, r9, r10, r11
      mov QWORD [env_label_class+32], rax
      mov QWORD [rax+8], new_

    ;=================================;
    ; End object initialization       ;
    ;=================================;
    ;execute main code
    jmp main_code


exit_program:

    ; $ Release stack frame
    leave

    ; Exit with exit code 0 (rbx)
    mov rax, 60
    mov rdi, 0
    syscall
;===============================================================================
; Reads a number from STDIN and returns it in RAX.
;===============================================================================
input_number:
    enter 0, 0

    ; Save all registers it modifies
    ; Registers modified by syscalls from here:
    ; https://en.wikibooks.org/wiki/X86_Assembly/Interfacing_with_Linux#syscall
    ; http://callumscode.com/blog/3
    multipush rbx, rcx, rdx, rsi, rdi, r8, r9, r10, r11

    ; The multiplier
    mov r8, 10

    ; Save the current pointer into register
    mov rsi, QWORD [buffer.current]

    ; If there is nothing left in the input buffer then we need to get more data
    cmp QWORD [buffer.remaining], 0
    jne .buffer_not_empty

        ; Read from STDIN -- number of bytes read is in RAX
        read

        ; If we read nothing then we are at EOF -- show error
        cmp rax, 0
        jne .read_no_eof

            mov BYTE [input_eof], 1
            jmp input_eof_error

        .read_no_eof:

    .buffer_not_empty:

    ; We will save the sign of our number here
    xor r9, r9

    ; Check for negative number
    debug_rsi
    cmp BYTE [rsi], '-'
    jne .number_not_negative

        ; Set sign register to 1
        inc r9
        ; Move forward in our buffer
        inc_rsi

    .number_not_negative:

    ; We will accumulate our number in RAX and use RBX for the incoming digits
    xor rax, rax
    xor rbx, rbx

    .read_loop:
        ; If there is nothing left in the input buffer then we need to get more data
        cmp QWORD [buffer.remaining], 0
        jne .buffer_not_empty2

            ; Save RAX
            push rax
            ; Read from STDIN -- number of bytes read is in RAX
            read

            ; If we read nothing then we are at EOF -- save it and exit the loop
            cmp rax, 0
            jne .read_no_eof2

                mov BYTE [input_eof], 1
                ; Restore RAX
                pop rax
                jmp .read_loop_exit

            .read_no_eof2:
            ; Restore RAX
            pop rax

        .buffer_not_empty2:

        debug_rsi

        ; If we read a newline then we increment and exit the loop
        cmp BYTE [rsi], 10
        jne .not_newline

            ; Increment our buffer and exit the loop
            inc_rsi
            jmp .read_loop_exit

        .not_newline:

        ; If we read something other than '0'-'9' then show error
        cmp BYTE [rsi], '0'
        jb input_error
        cmp BYTE [rsi], '9'
        ja input_error

        ; Now we have only '0'-'9' left and convert the ASCII value to a digit
        mov bl, BYTE [rsi]
        sub rbx, '0'
        ; Multiply the number we already have by 10 and add the new digit
        mul r8
        add rax, rbx

        ; Go forward
        inc_rsi

        jmp .read_loop


    .read_loop_exit:

    ; If we have nothing more to read this may be our last number we can get
    ; from STDIN -- so better check again and maybe set input_eof
    cmp QWORD [buffer.remaining], 0
    jne .buffer_not_empty3

        ; Save RAX
        push rax
        ; Read from STDIN -- number of bytes read is in RAX
        read

        ; If we read nothing then we are at EOF
        cmp rax, 0
        jne .read_no_eof1

            mov BYTE [input_eof], 1

        .read_no_eof1:
        ; Restore RAX
        pop rax

    .buffer_not_empty3:

    cmp r9, 1
    jne .number_dont_negate

        neg rax

    .number_dont_negate:

    .return:
    ; Save current buffer pointer to memory
    mov QWORD [buffer.current], rsi

    ; Restore all saved registers
    multipop rbx, rcx, rdx, rsi, rdi, r8, r9, r10, r11

    ; End function
    leave
    ret

;===============================================================================
; Returns the boolean value of EOF in RAX.
;===============================================================================
eof:
    ; Copy the eof value to rax
    xor rax, rax
    mov al, BYTE [input_eof]
    ret

;===============================================================================
; Prints out the error on seeing forbidden characters while trying to read from
; STDIN and exits with exit code 1.
; All allowed characters are: '0'-'9', '\n' and '-'
;===============================================================================
input_error:
    ; Move the erroneous symbol (which is in [rsi]) to the correct position in
    ; our error string
    mov rax, error_message
    add rax, error_message.len
    sub rax, 3
    mov bl, BYTE [rsi]
    mov BYTE [rax], bl

    ; Output error message
    mov rax, 1
    mov rdi, 1
    mov rsi, error_message
    mov rdx, error_message.len
    syscall

    ; Exit with exit code 1 (rbx)
    mov rax, 60
    mov rdi, 1
    syscall

;===============================================================================
; Prints out the error on hitting EOF while trying to read from STDIN and exits
; with exit code 2.
;===============================================================================
input_eof_error:
    ; Output eof error message
    mov rax, 1
    mov rdi, 1
    mov rsi, eof_error_message
    mov rdx, eof_error_message.len
    syscall

    ; Exit with exit code 2 (rbx)
    mov rax, 60
    mov rdi, 2
    syscall

;=================================================================================
;Prints out the error on hitting no linebreak or eof while trying to read a character
; from STDIN and exits with exit code 2
;=================================================================================
input_char_error:
    ; Output eof error message
    mov rax, 1
    mov rdi, 1
    mov rsi, char_error_message
    mov rdx, char_error_message.len
    syscall

    ; Exit with exit code 2 (rbx)
    mov rax, 60
    mov rdi, 2
    syscall

;===============================================================================
; $ Prints out the error on failing memory allocation for an array.
;===============================================================================
alloc_error:
    ; Output alloc error message
    mov rax, 1
    mov rdi, 1
    mov rsi, alloc_error_message
    mov rdx, alloc_error_message.len
    syscall

    ; Exit with exit code 2 (rbx)
    mov rax, 60
    mov rdi, 2
    syscall

;===============================================================================
; $ Prints out the error on failing memory allocation for an array with negative length.
;===============================================================================
alloc_error2:
    ; Output second alloc error message
    mov rax, 1
    mov rdi, 1
    mov rsi, alloc_error2_message
    mov rdx, alloc_error2_message.len
    syscall

    ; Exit with exit code 2 (rbx)
    mov rax, 60
    mov rdi, 2
    syscall

;===============================================================================
; $ Prints out the error on array index out of bounds.
;===============================================================================
index_error:
    ; Output index error message
    mov rax, 1
    mov rdi, 1
    mov rsi, index_error_message
    mov rdx, index_error_message.len
    syscall

    ; Exit with exit code 2 (rbx)
    mov rax, 60
    mov rdi, 2
    syscall

;===============================================================================
; $ Prints out the error on missing return.
;===============================================================================
return_error:
    ; Output return error message
    mov rax, 1
    mov rdi, 1
    mov rsi, return_error_message
    mov rdx, return_error_message.len
    syscall

    ; Exit with exit code 2 (rbx)
    mov rax, 60
    mov rdi, 2
    syscall

;===============================================================================
; Receives a number in the RAX register and prints it to stdout with trailing
; newline.
;===============================================================================
output_number:
    ; Make room for 21 bytes
    enter 21, 0

    ; Save all registers it modifies
    multipush rbx, rcx, rdx, rsi, rdi, r8, r9, r10, r11

    ; Save number in rbx
    mov rbx, rax

    ; The divisor
    mov r8, 10

    ; We will use rsi as pointer to our data
    mov rsi, rbp
    dec rsi ; TODO: NOT SURE ABOUT THIS -- LOOK AT IT AGAIN

    ; Test for signedness -- if signed then output '-'
    test rbx, rbx
    jns .not_negative

        mov [rsi], BYTE '-'
        mov rax, 1
        mov rdi, 1
        mov rdx, 1
        syscall

        ; Now we will work on the positive number
        neg rbx

    .not_negative:

    ; We will need a newline at the end
    mov [rsi], BYTE 10
    mov rax, rbx

    ; This will hold the number of bytes we will write
    mov rcx, 1

    .not_zero:

        ; Move to next memory position, i.e. one to the "left"
        dec rsi
        ; We will output one character more
        inc rcx

        ; Get ready to divide and divide by 10
        xor rdx, rdx
        div r8
        ; Make ASCII digit from remainder
        add rdx, 48
        mov [rsi], BYTE dl

    cmp rax, 0
    jnz .not_zero


    ; Output the generated string
    mov rax, 1
    mov rdi, 1
    mov rdx, rcx
    syscall

    ; Restore all saved registers
    multipop rbx, rcx, rdx, rsi, rdi, r8, r9, r10, r11

    ; End function
    leave
    ret

;===============================================================================
; $ Receives a float in the XMM0 register and prints it to stdout with trailing
; newline.
;===============================================================================
output_float:
    enter 0, 0
        
    ; Save all registers it modifies
    multipush rcx, rdx, rsi, rdi, r8, r9, r10, r11
    multifpush xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7, xmm8, xmm9, xmm10, xmm11, xmm12, xmm13, xmm14, xmm15

    mov    rdi, float_formatout
    mov    rax, 1 ; 1 xmm register
    call printf

    multifpop xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7, xmm8, xmm9, xmm10, xmm11, xmm12, xmm13, xmm14, xmm15
    ; Restore all saved registers
    multipop rcx, rdx, rsi, rdi, r8, r9, r10, r11

    ; End function
    leave
    ret

;===============================================================================
; $ Reads a float from STDIN and returns it in XMM0.
;===============================================================================
input_float:
    enter 0, 0
    ; Save all registers it modifies
    multipush rcx, rdx, rsi, rdi, r8, r9, r10, r11
    multifpush xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7, xmm8, xmm9, xmm10, xmm11, xmm12, xmm13, xmm14, xmm15

    mov rdi, float_formatin
    mov rax, 1 ; 1 xmm register
    call scanf

    cvtps2pd xmm0,xmm0
    multifpop xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7, xmm8, xmm9, xmm10, xmm11, xmm12, xmm13, xmm14, xmm15
    ; Restore all saved registers
    multipop rcx, rdx, rsi, rdi, r8, r9, r10, r11

    ; End function
    leave
    ret


;===============================================================================
; $ Receives a character in the AL register and prints it to stdout with 
;trailing newline.
;===============================================================================
output_character:
    debug_rsi
    enter 1, 0
        
    ; Save all registers it modifies
    multipush rbx, rcx, rdx, rsi, rdi, r8, r9, r10, r11
    mov rsi, rbp
    mov [rsi], al
    debug_rsi
        mov rax, 1
        mov rdi, 1
        mov rdx, 1
        syscall
    
    mov [rsi], BYTE 10
        mov rax, 1
        mov rdi, 1
        mov rdx, 1
        syscall

    ; Restore all saved registers
    multipop rbx, rcx, rdx, rsi, rdi, r8, r9, r10, r11

    ; End function
    leave
    ret

;===============================================================================
; $ Reads a character from STDIN and returns it in AL.
;===============================================================================
input_character:
    enter 0, 0
    ; Save all registers it modifies
    multipush rbx, rcx, rdx, rsi, rdi, r8, r9, r10, r11

    ; Save the current pointer into register
    mov rsi, QWORD [buffer.current]

    ; If there is nothing left in the input buffer then we need to get more data
    cmp QWORD [buffer.remaining], 0
    jne .buffer_not_empty

      ;read from Input
      read

        ; If we read nothing then we are at EOF -- show error
        cmp rax, 0
        jne .read_no_eof

            mov BYTE [input_eof], 1
            jmp input_eof_error

        .read_no_eof:

    .buffer_not_empty:
    
    ;read Character
    debug_rsi
    mov bl, BYTE [rsi]
    
    ;increment rsi
    inc_rsi
    cmp QWORD [buffer.remaining],0
    jne .buffer_not_empty2   
    
      ;read from Input
      read

      cmp rax, 0
      jne .buffer_not_empty2
        mov BYTE [input_eof], 1
        jmp .read_exit

    .buffer_not_empty2:
      debug_rsi

      ; If we read a newline then we increment and exit the loop
      cmp BYTE [rsi], 10
      je .read_new_line
        
        jmp input_char_error

      .read_new_line:
      inc_rsi

  .read_exit:
    mov al, bl
    ; Restore all saved registers
    multipop rbx, rcx, rdx, rsi, rdi, r8, r9, r10, r11
    leave
    ret

;===============================================================================
; The new(ref class) function
;===============================================================================

new_:
  ;              ______________
  ;_____________/initialization\________________________________________________
  mov rax, rbp
  mov rbp, rsp
  sub rsp, 0
  mov rdx, rsp
  push rdx
  push rax
  multipush rbx, rcx, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15
  multifpush xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7
  mov rax, rsp
  mov rsp, rbp
  add rsp, 8
  ; pop reference to class
  pop rbx
  ; t4@1:double = call dummy
  push qword [rbp]
  mov [rdx-8], rsp
  mov rsp, rax

  ;              _____________
  ;_____________/function code\________________________________________________
  ; (1) check if rbx is a class
  cmp QWORD [rbx], env_class_class
  jne return_error
  ; (2) get label array
  mov r8, [rbx+8]
  ; (3) calculate size of object
  mov r9, [r8]
  imul r9, r9, 8
  add r9, 8
  ; (4) allociate memory
  multipush rcx, rsi, rdi, r8, r9, r10, r11
  mov rdi, r9
  call malloc
  test rax, rax
  jz alloc_error
  pop QWORD [rax]
  multipop rcx, rsi, rdi, r8, r9, r10, r11
  mov QWORD [rax], rbx
  ; (5) set default values
  mov r10, 8 ;counting variable
  .loop:
    cmp r10, r9
    je .end_loop
    add r8, 8
    mov r11, [r8]
    cmp QWORD [r11], 1
    je .array
    mov QWORD [rax+r10], 0
    add r10, 8
    jmp .loop
    .array:
    mov QWORD [rax+r10], empty_array
    add r10, 8
    jmp .loop
  .end_loop:
  mov rbx, rax
  ;            ___________
  ;___________/return code\_____________________________________________________
  .return_sequence:
  mov rdx, rbp
  sub rdx, 0
  sub rdx, 168
  .return_sequence2:
  cmp rsp, rdx
  jge .return_sequence3
  pop rdi
  cmp rdi, rbx
  je .return_sequence2
  jmp .return_sequence2
  .return_sequence3:
  mov rax, rbx
  multifpop xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7
  multipop rbx, rcx, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15
  pop rbp
  pop rsp
  ret
  

