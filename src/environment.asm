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
global type_void
global type_int
global type_double
global type_char
global type_ref  
global type_array_int
global type_array_double
global type_array_char
global type_array_ref
global eof
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

%macro allociate 1
  mov rax, %1 
  multipush rcx, rsi, rdi, r8, r9, r10, r11
  push rax
  imul rdi, rax, 8
  call malloc
  test rax, rax
  jz alloc_error
  pop QWORD [rax]
  multipop rcx, rsi, rdi, r8, r9, r10, r11
%endmacro

; Increment our rsi register (=buffer.current) and decrent the remaining bytes
%macro inc_rsi 0
    ; Move forward in our buffer
    inc rsi
    dec QWORD [buffer.remaining]
%endmacro

%macro debug 1
  push rax
  mov rax, %1
  call output_number
  pop rax
%endmacro

; Debugging macro, outputs the current value of [rsi]
%macro debug_rsi 0
    ; push rax
     ;xor rax, rax
     ;mov al, BYTE [rsi]
     ;add rax, 100000000
     ;call output_number
     ;mov rax, [buffer.remaining]
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
;================================================================================
; object-classs model
;================================================================================

;           _________________
;__________/Primitive classes\___________________________________________________

  class_primitive_int:
    dq handle_class
    dq class_class
    dq 1
    dq class_primitive_int_str
    dq empty_ref_obj
    dq empty_int_obj
    dq empty_ref_obj
    dq empty_int_obj 
  class_primitive_int_str:
    dq handle_object
    dq class_primitive_char
    dq 3
    dq 'i'
    dq 'n'
    dq 't'

  empty_int_obj:
    dq handle_object
    dq class_primitive_int
    dq 0

  class_primitive_double:
    dq handle_class
    dq class_class
    dq 1
    dq class_primitive_double_str
    dq empty_ref_obj
    dq empty_int_obj
    dq empty_ref_obj
    dq empty_int_obj 
  class_primitive_double_str:
    dq handle_object
    dq class_primitive_char
    dq 6
    dq 'd'
    dq 'o'
    dq 'u'
    dq 'b'
    dq 'l'
    dq 'e'

  class_primitive_char:
    dq handle_class
    dq class_class
    dq 1
    dq class_primitive_char_str
    dq empty_ref_obj
    dq empty_int_obj
    dq empty_ref_obj
    dq empty_int_obj 
  class_primitive_char_str:
    dq handle_object
    dq class_primitive_char
    dq 4
    dq 'c'
    dq 'h'
    dq 'a'
    dq 'r'

  class_primitive_ref:
    dq handle_class
    dq class_class
    dq 1
    dq class_primitive_ref_str
    dq empty_ref_obj
    dq empty_int_obj
    dq empty_ref_obj
    dq empty_int_obj 
  class_primitive_ref_str:
    dq handle_object
    dq class_primitive_char
    dq 3
    dq 'r'
    dq 'e'
    dq 'f'

  empty_ref_obj:
    dq handle_object
    dq class_primitive_ref
    dq 0

;                     ______________
;____________________/function class\___________________________________
  class_function:
    dq handle_class
    dq class_class
    dq 1
    dq class_function_str
    dq empty_ref_obj
    dq empty_int_obj
    dq class_function_attribute_labels
    dq class_function_attribute_offsets

  class_function_str:
    dq handle_object
    dq class_primitive_char
    dq 8
    dq 'f'
    dq 'u'
    dq 'n'
    dq 'c'
    dq 't'
    dq 'i'
    dq 'o'
    dq 'n'

  class_function_attribute_labels:
    dq handle_object
    dq class_primitive_ref
    dq 5
    dq label_env_handle
    dq label_env_parent
    dq label_env_length
    dq label_env_fparameter
    dq label_env_result

  class_function_attribute_offsets:
    dq handle_object
    dq class_primitive_int
    dq 5
    dq 0
    dq 8
    dq 16
    dq 24
    dq 32
   
  env_new_function_type:
    dq handle_object
    dq class_function
    dq 1
    dq env_new_function_type_param
    dq class_primitive_ref

  env_new_function_type_param:
    dq handle_object
    dq class_primitive_ref
    dq 0

;                     ___________
;____________________/class class\_______________________________________

  class_class:
    dq handle_class
    dq class_class
    dq 1
    dq class_class_str
    dq class_class_function_label
    dq class_class_function_address
    dq class_class_attribute_label
    dq class_class_attribute_offset

  class_class_str:
    dq handle_object
    dq class_primitive_char
    dq 5
    dq 'c'
    dq 'l'
    dq 'a'
    dq 's'
    dq 's'

  class_class_function_label:
    dq handle_object
    dq class_primitive_ref
    dq 1
    dq label_env_new

  class_class_function_address:
    dq handle_object
    dq class_primitive_int
    dq 1
    dq new_

  class_class_attribute_label:
    dq handle_object
    dq class_primitive_ref
    dq 8
    dq label_env_handle
    dq label_env_parent
    dq label_env_length
    dq label_env_name
    dq label_env_funcLabels
    dq label_env_funcAddress
    dq label_env_attrLabels
    dq label_env_attrOffsets

  class_class_attribute_offset:
    dq handle_object
    dq class_primitive_int
    dq 8
    dq 0
    dq 8
    dq 16
    dq 24
    dq 32
    dq 40
    dq 48
    dq 56
    
;                  ___________
;_________________/label class\___________________

  class_label:
    dq handle_class
    dq class_class
    dq 1
    dq class_label_str
    dq empty_ref_obj
    dq empty_int_obj
    dq class_label_attribute_labels
    dq class_label_attribute_offsets

  class_label_str:
    dq handle_object
    dq class_primitive_char
    dq 5
    dq 'l'
    dq 'a'
    dq 'b'
    dq 'e'
    dq 'l'

  class_label_attribute_labels:
    dq handle_object
    dq class_primitive_ref
    dq 6
    dq label_env_handle
    dq label_env_parent
    dq label_env_length
    dq label_env_name
    dq label_env_type
    dq label_env_index

  class_label_attribute_offsets:
    dq handle_object
    dq class_primitive_int
    dq 6
    dq 0
    dq 8
    dq 16
    dq 24
    dq 32
    dq 40

;               _____________
;______________/Message Class\__________________________

  class_message_set:
    dq handle_class
    dq class_class
    dq 1
    dq class_message_set_str
    dq empty_ref_obj
    dq empty_int_obj
    dq class_message_set_labels
    dq class_message_set_offsets

  class_message_set_str:
    dq handle_object
    dq class_primitive_char
    dq 3
    dq 'S'
    dq 'E'
    dq 'T'

  class_message_set_labels:
    dq handle_object
    dq class_primitive_ref
    dq 5
    dq label_env_handle
    dq label_env_parent
    dq label_env_length
    dq label_env_key ; a label
    dq label_env_value

  class_message_set_offsets:
    dq handle_object
    dq class_primitive_int
    dq 5
    dq 0
    dq 8
    dq 16
    dq 24
    dq 32



  class_message_get:
    dq handle_class
    dq class_class
    dq 1
    dq class_message_get_str
    dq empty_ref_obj
    dq empty_int_obj
    dq class_message_get_labels
    dq class_message_get_offsets

  class_message_get_str:
    dq handle_object
    dq class_primitive_char
    dq 3
    dq 'G'
    dq 'E'
    dq 'T'

  class_message_get_labels:
    dq handle_object
    dq class_primitive_ref
    dq 5
    dq label_env_handle
    dq label_env_parent
    dq label_env_length
    dq label_env_key ; a label
    dq label_env_value

  class_message_get_offsets:
    dq handle_object
    dq class_primitive_int
    dq 5
    dq 0
    dq 8
    dq 16
    dq 24
    dq 32

  class_message_function:
    dq handle_class
    dq class_class
    dq 1
    dq class_message_function_str
    dq empty_ref_obj
    dq empty_int_obj
    dq class_message_function_labels
    dq class_message_function_offsets

  class_message_function_str:
    dq handle_object
    dq class_primitive_char
    dq 6
    dq 'M'
    dq 'E'
    dq 'T'
    dq 'H'
    dq 'O'
    dq 'D'

  class_message_function_labels:
    dq handle_object
    dq class_primitive_ref
    dq 7
    dq label_env_handle
    dq label_env_parent
    dq label_env_length
    dq label_env_key
    dq label_env_result
    dq label_env_parameter
    dq label_env_callee

  class_message_function_offsets:
    dq handle_object
    dq class_primitive_int
    dq 7
    dq 0
    dq 8
    dq 16
    dq 24
    dq 32
    dq 40
    dq 48
;               ______
;______________/labels\_________________________________

  label_env_new:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_new_str
    dq env_new_function_type
    dq 0

  label_env_new_str:
    dq handle_object
    dq class_primitive_char
    dq 7
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'n'
    dq 'e'
    dq 'w'

  label_env_handle:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_handle_str
    dq class_primitive_int
    dq 0

  label_env_handle_str:
    dq handle_object
    dq class_primitive_char
    dq 10
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'h'
    dq 'a'
    dq 'n'
    dq 'd'
    dq 'l'
    dq 'e'

  label_env_parent:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_parent_str
    dq class_primitive_ref
    dq 1
  
  label_env_parent_str:
    dq handle_object
    dq class_primitive_char
    dq 10
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'p'
    dq 'a'
    dq 'r'
    dq 'e'
    dq 'n'
    dq 't'

  label_env_length:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_length_str
    dq class_primitive_int
    dq 2

  label_env_length_str:
    dq handle_object
    dq class_primitive_char
    dq 10
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'l'
    dq 'e'
    dq 'n'
    dq 'g'
    dq 't'
    dq 'h'

  label_env_name:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_name_str
    dq class_primitive_ref
    dq 3

  label_env_name_str:
    dq handle_object
    dq class_primitive_char
    dq 8
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'n'
    dq 'a'
    dq 'm'
    dq 'e'

  label_env_funcLabels:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_funcLabels_str
    dq class_primitive_ref
    dq 4

  label_env_funcLabels_str:
    dq handle_object
    dq class_primitive_char
    dq 14
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'f'
    dq 'u'
    dq 'n'
    dq 'c'
    dq 'L'
    dq 'a'
    dq 'b'
    dq 'e'
    dq 'l'
    dq 's'

  label_env_funcAddress:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_funcAddress_str
    dq class_primitive_ref
    dq 5

  label_env_funcAddress_str:
    dq handle_object
    dq class_primitive_char
    dq 15
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'f'
    dq 'u'
    dq 'n'
    dq 'c'
    dq 'A'
    dq 'd'
    dq 'd'
    dq 'r'
    dq 'e'
    dq 's'
    dq 's'

  label_env_attrLabels:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_attrLabels_str
    dq class_primitive_ref
    dq 6

  label_env_attrLabels_str:
    dq handle_object
    dq class_primitive_char
    dq 14
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'a'
    dq 't'
    dq 't'
    dq 'r'
    dq 'L'
    dq 'a'
    dq 'b'
    dq 'e'
    dq 'l'
    dq 's'

  label_env_attrOffsets:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_attrOffsets_str
    dq class_primitive_ref
    dq 7

  label_env_attrOffsets_str:
    dq handle_object
    dq class_primitive_char
    dq 15
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'a'
    dq 't'
    dq 't'
    dq 'r'
    dq 'O'
    dq 'f'
    dq 'f'
    dq 's'
    dq 'e'
    dq 't'
    dq 's'

  label_env_type:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_type_str
    dq class_primitive_ref
    dq 4
   
  label_env_type_str:
    dq handle_object
    dq class_primitive_char
    dq 8
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 't'
    dq 'y'
    dq 'p'
    dq 'e'

  label_env_index:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_index_str
    dq class_primitive_int
    dq 5

  label_env_index_str:
    dq handle_object
    dq class_primitive_char
    dq 8
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'i'
    dq 'n'
    dq 'd'
    dq 'e'
    dq 'x'
 
  label_env_key:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_key_str
    dq class_primitive_ref
    dq 3

  label_env_key_str:
    dq handle_object
    dq class_primitive_char
    dq 7
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'k'
    dq 'e'
    dq 'y'
    
  label_env_parameter:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_parameter_str
    dq class_primitive_ref
    dq 5

  label_env_parameter_str:
    dq handle_object
    dq class_primitive_char
    dq 13
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'p'
    dq 'a'
    dq 'r'
    dq 'a'
    dq 'm'
    dq 'e'
    dq 't'
    dq 'e'
    dq 'r'
    
  label_env_callee:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_callee_str
    dq class_primitive_ref
    dq 6

  label_env_callee_str:
    dq handle_object
    dq class_primitive_char
    dq 10
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'c'
    dq 'a'
    dq 'l'
    dq 'l'
    dq 'e'
    dq 'e'

  label_env_result:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_result_str
    dq class_primitive_ref
    dq 4

  label_env_result_str:
    dq handle_object
    dq class_primitive_char
    dq 10
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'r'
    dq 'e'
    dq 's'
    dq 'u'
    dq 'l'
    dq 't'

  label_env_value:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_value_str
    dq class_primitive_ref
    dq 4

  label_env_value_str:
    dq handle_object
    dq class_primitive_char
    dq 9
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'v'
    dq 'a'
    dq 'l'
    dq 'u'
    dq 'e'

  label_env_fparameter:
    dq handle_object
    dq class_label
    dq 1
    dq label_env_fparameter_str
    dq class_primitive_ref
    dq 3

  label_env_fparameter_str:
    dq handle_object
    dq class_primitive_char
    dq 14
    dq 'e'
    dq 'n'
    dq 'v'
    dq ':'
    dq 'f'
    dq 'p'
    dq 'a'
    dq 'r'
    dq 'a'
    dq 'm'
    dq 'e'
    dq 't'
    dq 'e'
    dq 'r'

    ; empty array
    empty_array: dq 0

    ;primitive types
    type_void: dq 0, 0
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
            debug_rsi
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
    ;cmp QWORD [buffer.remaining], 0
    ;jne .buffer_not_empty3

        ; Save RAX
     ;   push rax
        ; Read from STDIN -- number of bytes read is in RAX
      ;  read

        ; If we read nothing then we are at EOF
       ; cmp rax, 0
        ;jne .read_no_eof1

         ;   mov BYTE [input_eof], 1

        ;.read_no_eof1:
        ; Restore RAX
        ;pop rax

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
  
;===============================================================================
; Handle a message for a class
;===============================================================================
handle_class:
  mov rax, rsp
  multipush rbx, rcx, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15
  mov r12, [rax+16] ; r12 = object
  mov r14, [rax+8]  ; r14 = message
  mov r15, [r14 +8] ; rdx = class of message
  cmp QWORD [rdx], class_message_set
  je .set
  cmp QWORD [rdx], class_message_get
  je .get
  cmp QWORD [rdx], class_message_function
  je handle_object.function

;                   ___
;__________________(set\_______________________________________________________
  .set:
    mov rbx, [r14+24]; rbx = key:label
    mov rcx, [rbx+32]; rcx = type of label
    cmp rcx, class_function
    jne .setAttribute
    mov r10, [r12+32]; r10 = array of Labels
    mov r11, [r12+40]; r11 = array of functions 
    mov rcx, [rbx+40]; rcx = index of label
    cmp QWORD[r10+16], rcx
    jle index_error
    cmp QWORD[r10+rcx*8], rbx
    je .returnSet
      ;TODO search for Label
      .returnSet:
        mov rax, [r14+32] ; rax = value object
        mov rbx, [rax+24] ; rbx = value
        mov QWORD[r11+24+rcx*8], rbx
        jmp .returnSeq
    
  .setAttribute:
    mov r10, [r12+48]; r10 = array of Labels
    mov r11, [r12+56]; r11 = array of offsets 
    mov rcx, [rbx+40]; rcx = index of label
    cmp QWORD[r10+16], rcx
    jle index_error
    cmp QWORD[r10+rcx*8], rbx
    je .attrreturnSet
      ;TODO search for Label
      .attrreturnSet:
        mov rax, [r14+32] ; rax = value object
        mov rbx, [rax+24] ; rbx = value
        mov QWORD[r11+24+rcx*8], rbx
        jmp .returnSeq
;                  ___
;_________________/get\________________________________________________________
  .get:
    mov rbx, [r14+24]; rbx = key:label
    mov rcx, [rbx+32]; rcx = type of label
    cmp rcx, class_function
    jne .getAttribute
    mov r10, [r12+32]; r10 = array of labels
    mov r11, [r12+40]; r11 = array of functions
    mov rcx, [rbx+40]; rcx = index of label
    cmp QWORD[r10+16], rcx
    jle index_error
    cmp QWORD[r10+24+rcx*8], rbx
    je .returnGet
      ;TODO search for Label
      .returnGet:
        mov rbx, [r11+24+rcx*8] ; rbx = value
        ;--- create object
        allociate 4
        mov QWORD [rax], handle_object
        mov QWORD [rax+8], class_primitive_int
        mov QWORD [rax+16], 1
        mov QWORD [rax+24], rbx
        ;---
        mov QWORD[r14+32], rax
        jmp .returnSeq

  .getAttribute:
    mov r10, [r12+48]; r10 = array of labels
    mov r11, [r12+56]; r11 = array of offsets
    mov rcx, [rbx+40]; rcx = index of label
    cmp QWORD[r10+16], rcx
    jle index_error
    cmp QWORD[r10+24+rcx*8], rbx
    je .attrreturnGet
      ;TODO search for Label
      .attrreturnGet:
        mov rbx, [r11+24+rcx*8] ; rbx = value
        ;--- create object
        allociate 4
        mov QWORD [rax], handle_object
        mov QWORD [rax+8], class_primitive_int
        mov QWORD [rax+16], 1
        mov QWORD [rax+24], rbx
        ;---
        mov QWORD[r14+32], rax
        jmp .returnSeq

  .returnSeq:
  multipop rbx, rcx, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15
  ret

;================================================================================
; handle object
;================================================================================
handle_object:
  mov rax, rsp
  multipush rbx, rcx, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15
  mov r14, [rax+16] ; r14 = object
  mov r15, [rax+8]  ; r15 = message
  mov rdx, [r15 +8] ; rdx = class of message
  cmp QWORD [rdx], class_message_set
  je .set
  cmp QWORD [rdx], class_message_get
  je .get
  cmp QWORD [rdx], class_message_function
  je .function
;                      ___
;_____________________/get\_______________________________________________________
  .set:
    mov r13, [r15+24]; r13 = key:label
    mov r8, [r14+8] ; r8 = class of object
    mov r9, [r8]; r9 = handle method of class
    ;-- create get-message
    allociate 5
    mov QWORD [rax], handle_object
    mov QWORD [rax+8], class_message_get
    mov QWORD [rax+16], 1
    mov QWORD [rax+24], r13
    ;--
    push QWORD r8
    push QWORD rax
    call r9
    pop rax ; rax = getMessage
    add rsp, 8
    mov r8, [rax+32]; r8 = return object
    mov r9, [r8+24]; r9 = offset
    mov r12, [r15+32]; r12 = value object
    mov QWORD [r14+r9], r12
    jmp .returnSeq
;                      ___
;_____________________/set\_______________________________________________________
  .get:
    mov r13, [r15+24]; r13 = key:label
    mov r8, [r14+8] ; r8 = class of object
    mov r9, [r8]; r9 = handle method of class
    ;-- create get-message
    allociate 5
    mov QWORD [rax], handle_object
    mov QWORD [rax+8], class_message_get
    mov QWORD [rax+16], 1
    mov QWORD [rax+24], r13
    ;--
    push QWORD r8
    push QWORD rax
    call r9
    pop rax ; rax = getMessage
    add rsp, 8
    mov r8, [rax+32]; r8 = return object
    mov r9, [r8+24]; r9 = offset
    mov r12, [r14+r9]; r12 = value object
    mov QWORD [r15+32], r12
    jmp .returnSeq
;                      ________
;_____________________/function\__________________________________________________
  .function:
    mov r13, [r15+24]; r13 = key:label
    mov r8, [r14+8] ; r8 = class of object
    mov r9, [r8]; r9 = handle method of class
    ;-- create get-message
    allociate 5
    mov QWORD [rax], handle_object
    mov QWORD [rax+8], class_message_get
    mov QWORD [rax+16], 1
    mov QWORD [rax+24], r13
    ;--
    push QWORD r8
    push QWORD rax
    call r9
    pop rax ; rax = getMessage
    add rsp, 8
    mov r8, [rax+32]; r8 = return object
    mov r9, [r8+24]; r9 = address

    mov r8, [r15+40]; r8 = parameter array
    push r14
    mov r11, [r8+16]; r11 = parameter count
    imul r10, r11, 8
    add r10, r8; r10 = last parameter address
    mov rbx, [r8+24]; rbx = current parameter
    .parameter_loop:
      cmp rbx, r10
      jg .end_parameter_loop
      mov rcx, [rbx]; rcx = current parameter object
      push QWORD [rcx+24]
      add rbx, 8
      jmp .parameter_loop
    .end_parameter_loop:
    call r9; call method/ result is in rax
    imul r11, r11, 8
    add rsp, r11; pop parameter
    add rsp, 8; pop self reference
    mov rbx, rax; rbx = result of functioncall
    mov r8, [r13+32]; r8 = type /hopfull it is a class_function TODO
    mov r9, [r8+56]; r9 = return type
    ;-- create object
    allociate 4
    mov QWORD [rax], handle_object
    mov QWORD [rax+8], r9
    mov QWORD [rax+16], 1
    mov QWORD [rax+24], rbx
    ;--
    mov QWORD[r15+32], rax
    jmp .returnSeq   
    
  .returnSeq:
  multipop rbx, rcx, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15
  ret
