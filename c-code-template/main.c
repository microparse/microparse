#include <stdio.h>
#include <stdbool.h>
#include <assert.h>

#define INF -1
#define NINF -2

// functiona callback
// typedef void (*FunctionCallback)(int);
// FunctionCallback grammar_constructs[] = { &tag_cons, &len_cons, &case_cons, &repeat_cons };

typedef enum {
    BIT,
    BYTE
} dataunit;

typedef enum {
    LSB,
    MSB
} endianness;

typedef enum {
    TAG,
    LEN,
    REPEAT,
    CASE
} cons_t;

typedef struct {
    int start_byte;
    int start_bit;
    int end_byte;
    int end_bit;
} parsed_result;

int cur_byte_pos = 0;
int cur_bit_pos = 0;

int save_head_byte_pos;
int save_head_bit_pos;

const char* TAPE = "\xF2\xFF\xFF"; 
const int TAPE_LEN = 3;


/*@requires TAPE_LEN >= 0;
  requires \valid_read(((char*)TAPE)+(0..TAPE_LEN));
  requires cur_byte_pos < TAPE_LEN;
  requires cur_byte_pos >= 0;
  requires cur_bit_pos >= 0;
  requires cur_bit_pos <= 31;
  
  assigns cur_byte_pos, cur_bit_pos;
  
  ensures cur_bit_pos >= 0 && cur_bit_pos <= 8;
  ensures cur_byte_pos >= 0 && cur_byte_pos <= TAPE_LEN;
*/
bool get_next_bit() {
    bool cur_symbol;

    // assert(cur_byte_pos < TAPE_LEN);
    char cur_char = TAPE[cur_byte_pos];
    //@assert cur_bit_pos < 32;
    cur_symbol = 1 & (cur_char >> cur_bit_pos);
    // printf("Read %d from tape at loc %d\n", cur_symbol, cur_byte_pos*8+cur_bit_pos);
    //@assert cur_byte_pos + 1 < 2147483647;
    cur_bit_pos++;
    if (cur_bit_pos >= 8) {
        cur_bit_pos = cur_bit_pos % 8;
        cur_byte_pos++;
    }

    return cur_symbol;
}


/*@requires TAPE_LEN >= 0;
  requires \valid_read(TAPE+(0..(TAPE_LEN-1)));
  requires cur_byte_pos <= TAPE_LEN;
  requires cur_byte_pos >= 0;
  requires cur_bit_pos >= 0;
  requires cur_bit_pos <= 8;
  assigns \nothing;
  ensures (\result == 0) || (\result == 1);
*/
bool is_tape_available() {
    if ((cur_byte_pos + 1) < TAPE_LEN) {
        // some bytes remaining
        return 1;
    } else {
        if ((cur_byte_pos + 1) == TAPE_LEN) {
            // some bits left
            if (cur_bit_pos < 7) {
                return 1;
            }
        }
    }
    return 0;
}

/*@requires \valid(r);
  requires cur_bit_pos >= 0 && cur_bit_pos <= 8;
  requires cur_byte_pos >= 0 && cur_byte_pos <= TAPE_LEN;
  assigns *r;
*/
void set_pos_end(parsed_result* r)
{
    r->end_bit  = cur_bit_pos;
    r->end_byte = cur_byte_pos;
    return;
}

/*@requires \valid(r);
  requires \separated(r, &cur_byte_pos, &cur_bit_pos);
  requires cur_bit_pos >= 0 && cur_bit_pos <= 8;
  requires cur_byte_pos >= 0 && cur_byte_pos <= TAPE_LEN;
  assigns *r;
*/
void set_pos_start(parsed_result* r)
{
    r->start_bit  = cur_bit_pos;
    r->start_byte = cur_byte_pos;
    return;
}


/*@requires TAPE_LEN >= 0;
  requires \valid_read(((char*)TAPE)+(0..TAPE_LEN));
  requires cur_byte_pos < TAPE_LEN;
  requires cur_byte_pos >= 0;
  requires cur_bit_pos >= 0;
  requires cur_bit_pos < 8;
  
  assigns cur_byte_pos;
  
  ensures cur_bit_pos >= 0 && cur_bit_pos <= 8;
  ensures cur_byte_pos >= 0 && cur_byte_pos <= TAPE_LEN;
*/
unsigned char get_next_byte() {
    char cur_char = TAPE[cur_byte_pos];
    // printf("Read %d from tape at loc %d\n", cur_char, cur_byte_pos);
    cur_byte_pos++;
    /*@assert cur_byte_pos >= 0;*/
    return cur_char;
}

/*@requires TAPE_LEN >= 0;
  requires cur_byte_pos <= TAPE_LEN;
  requires cur_byte_pos >= 0;
  requires cur_bit_pos >= 0;
  requires cur_bit_pos <= 8;
  assigns \nothing;
  ensures \result >= 0;
*/
int remaining_bits() {
    int remaining_bytes = TAPE_LEN - cur_byte_pos;
    int remaining_bits;
    if (cur_bit_pos == 0) {
        remaining_bits = 0;
    } else {
        remaining_bits = 8 - cur_bit_pos;
    }

    return (8 * remaining_bytes) + remaining_bits;
}

/*@requires TAPE_LEN >= 0;
  requires cur_byte_pos <= TAPE_LEN;
  requires cur_byte_pos >= 0;
  requires cur_bit_pos >= 0;
  requires cur_bit_pos <= 8;
  assigns \nothing;
  ensures \result >= 0;
*/
int remaining_bytes() {
    int remaining_bytes = TAPE_LEN - cur_byte_pos;
    return remaining_bytes;
}

// set the value of the register to T
/*@requires size > 0;
  requires cur_byte_pos <= TAPE_LEN;
  requires cur_byte_pos >= 0;
  requires cur_bit_pos >= 0;
  requires cur_bit_pos <= 8;
  requires ((unit == BIT) ==> size <= 32) && ((unit == BYTE) ==> size <= 4);
  assigns \nothing;
*/
int tag_cons(dataunit unit, int size) {
    unsigned int tag_val;

    if (unit == BIT) {
        /*@ loop invariant 0 <= i < size;
          loop assigns tag_val;
          loop variant size;*/
        for (int i = 0; i < size; ++i) {
            tag_val = tag_val | get_next_bit();
            tag_val = tag_val << 1;
        }
        //@ assert tag_val >= 0;
    } else {
        assert(size <= 4);
        /*@ loop invariant 0 <= i < size;
          loop assigns tag_val;
          loop variant size;*/
        for (int i = 0; i < size; ++i) {
            tag_val = get_next_byte();
            tag_val = tag_val << 8;
        }
        //@ assert tag_val >= 0;
    }
    return tag_val;
};

// set the value of the counter register to L.
/*@requires TAPE_LEN >= 0;
  requires \valid_read(TAPE+(0..(TAPE_LEN-1)));
  requires cur_byte_pos <= TAPE_LEN;
  requires cur_byte_pos >= 0;
  requires cur_bit_pos >= 0;
  requires cur_bit_pos <= 8;
  requires size > 0;
  requires ((unit == BIT) ==> size <= 32) && ((unit == BYTE) ==> size <= 4);
  assigns \nothing;
*/
int len_cons(dataunit unit, endianness e, int size) {
    int len_val = 0;
    if (unit == BIT) {
        int i = 0;
        /*@loop invariant 0 <= i < size;
          loop assigns len_val;
          loop variant size;*/
        for (i = 0; i < size; ++i) {
            len_val = len_val | get_next_bit();
            len_val = len_val << 1;
        }
        //@ assert len_val >= 0;
    } else {
        int i = 0;
        // assert(size <= 4);
        //@ requires size <= 4;
        //@ assert unit == BYTE;
        /*@loop invariant 0 <= i < size;
          loop assigns len_val;
          loop variant size;*/
        for (i = 0; i < size; ++i) {
            len_val = get_next_byte();
            len_val = len_val << 8;
        }
        //@ assert len_val >= 0;
    }

    // if (unit == BIT) {
    //     if (remaining_bits() < len_val) {
    //         // error
    //         debug_write("len: err\n");
    //     }
    // } else {
    //     if (remaining_bytes() < len_val) {
    //         debug_write("len:err\n");
    //     }
    // }
    // return read value
    return len_val;
};

// make lookup table and call that function.
// case function: generate this with code
// repeats construct r, n times

/*@requires TAPE_LEN >= 0;
  requires \valid_read(TAPE+(0..(TAPE_LEN-1)));
  requires cur_byte_pos <= TAPE_LEN;
  requires cur_byte_pos >= 0;
  requires cur_bit_pos >= 0;
  requires cur_bit_pos <= 8;
  requires n > 0 || min > 0 || max > 0;
  assigns \nothing;
*/
parsed_result repeat_cons(dataunit u, int n, int min, int max) {
    parsed_result r;
    set_pos_start(&r);
    if (n == INF) {
        // at least min items and at most max items
        if (u == BIT) {
            int i = 0;
            /*@ loop invariant  0 <= i <= min;
               loop assigns \nothing;
               loop variant min;*/
            for (i = 0; i < min; ++i) {
                get_next_bit();
            }
            /*@ loop invariant  0 <= i <= max;
               loop assigns \nothing;
               loop variant max;*/
            while (i <= max) {
                if (is_tape_available()) {
                    break;
                }
                get_next_bit();
                i++;
            }

            set_pos_end(&r);
            return r;
        } else {
            int i = 0;

            /*@ loop invariant  0 <= i <= min;
               loop assigns \nothing;
               loop variant min;*/
            for (i = 0; i < min; ++i) {
                get_next_byte();
            }

            /*@ loop invariant  0 <= i <= max;
               loop assigns \nothing;
               loop variant max;*/
            while (i <= max) {
                if (is_tape_available()) {
                    break;
                }
                get_next_byte();
            }

            set_pos_end(&r);
            return r;
        }
    } else {
        if (u == BIT) {
            assert(n <= 8);
            /*@loop invariant  0 <= i < n;
              loop assigns \nothing;
              loop variant n;*/
            for (int i = 0; i < n; ++i) {
                get_next_bit();
            }
            set_pos_end(&r);
            return r;
        } else {
            /*@loop invariant  0 <= i < n;
               loop assigns \nothing;
               loop variant n;*/
            for (int i = 0; i < n; ++i) {
                get_next_byte();
            }
            set_pos_end(&r);
            return r;
        }
    }
};


// We define a gloabl list of registers which store results.
/*@ assigns \nothing;
*/
unsigned int run_parser(char* input_buffer, int buffer_len) {
    // PDU
    int reg4144 = tag_cons(BIT, 4);
    // RFU
    int reg4145 = tag_cons(BIT, 1);
    // ChSel
    int reg4146 = tag_cons(BIT, 1);
    // TxAdd
    int reg4147 = tag_cons(BIT, 1);
    // RxAdd
    int reg4148 = tag_cons(BIT, 1);
    int reg4149 = len_cons(BYTE, LSB, 2);

    switch (reg4144) {
        case 0b0001: {
                         // :ADV_DIRECT_IND
                         // AdvA
                         parsed_result  reg4150 = repeat_cons(BYTE, 6, NINF, INF);
                         // Target A
                         parsed_result  reg4151 = repeat_cons(BYTE, 6, NINF, INF);
                         break;
                     }
        case 0b0011: {
                         // :SCAN_REQ
                         // ScanA
                         parsed_result  reg4152 = repeat_cons(BYTE, 6, NINF, INF);
                         // AdvA
                         parsed_result  reg4153 = repeat_cons(BYTE, 6, NINF, INF);
                         break;
                     }
        case 0b0000: {
                     // :ADV_IDV
                     // AdvA
                     parsed_result  reg4154 = repeat_cons(BYTE, 6, NINF, INF);
                     // repeat 0 31 bytes
                     parsed_result  reg4155 = repeat_cons(BYTE, INF, 0, 31);
                     break;
                 }
        case 0b0101: {
                         // :CONNECT_IND
                         // InitA
                         parsed_result  reg4156 = repeat_cons(BYTE, 6, NINF, INF);
                         // AdvA
                         parsed_result  reg4157 = repeat_cons(BYTE, 6, NINF, INF);
                         // AA
                         parsed_result  reg4158 = repeat_cons(BYTE, 4, NINF, INF);
                         // CRCInit
                         parsed_result  reg4159 = repeat_cons(BYTE, 3, NINF, INF);
                         // WinSize
                         parsed_result  reg4160 = repeat_cons(BYTE, 1, NINF, INF);
                         // WinOffset
                         parsed_result  reg4161 = repeat_cons(BYTE, 2, NINF, INF);
                         // Interval
                         parsed_result  reg4162 = repeat_cons(BYTE, 2, NINF, INF);
                         // Latency
                         parsed_result  reg4163 = repeat_cons(BYTE, 2, NINF, INF);
                         // Timeout
                         parsed_result  reg4164 = repeat_cons(BYTE, 2, NINF, INF);
                         // ChM
                         parsed_result  reg4165 = repeat_cons(BYTE, 5, NINF, INF);
                         // Hop
                         parsed_result  reg4166 = repeat_cons(BYTE, 5, NINF, INF);
                         // SCA
                         parsed_result  reg4167 = repeat_cons(BYTE, 3, NINF, INF);
                         break;
                     }
        case 0b0010: {
                         // :ADV_NONCONN_IND
                         // AdvA
                         parsed_result  reg4168 = repeat_cons(BYTE, 6, NINF, INF);
                         // repeat 0 31 bytes
                         parsed_result  reg4169 = repeat_cons(BYTE, INF, 0, 31);
                         break;
                     }
        case 0b0111: {
                         // :ADV_EXT_IND
                         int reg4170 = len_cons(BIT, LSB, 6);
                         // AdvMode
                         parsed_result  reg4171 = repeat_cons(BYTE, 2, NINF, INF);
                         if (reg4170 == 0) {} else {
                             // repeat 0 63 bytes
                             parsed_result  reg4172 = repeat_cons(BYTE, reg4170, 0, 63);
                         }
                         // repeat 0 - 254 bytes
                         parsed_result  reg4173 = repeat_cons(BYTE, INF, 0, 254);
                         break;
                     }
        case 0b1000: {
                         // :AUX_CONNECT_RSP
                         int reg4174 = len_cons(BIT, LSB, 6);
                         // AdvMode
                         parsed_result  reg4175 = repeat_cons(BYTE, 2, NINF, INF);
                         if (reg4174 == 0) {} else {
                             // repeat 0 63 bytes
                             parsed_result  reg4176 = repeat_cons(BYTE, reg4174, 0, 63);
                         }
                         // repeat 0 - 254 bytes
                         parsed_result  reg4177 = repeat_cons(BYTE, INF, 0, 254);
                         break;
                     }
        case 0b0100: {
                         // :SCAN_RSP
                         // AdvA
                         parsed_result  reg4178 = repeat_cons(BYTE, 6, NINF, INF);
                         // repeat 0 31 bytes
                         parsed_result  reg4179 = repeat_cons(BYTE, INF, 0, 31);
                         break;
                     }
        case 0b0110: {
                         // :ADV_SCAN_IND
                         // AdvA
                         parsed_result  reg4180 = repeat_cons(BYTE, 6, NINF, INF);
                         // repeat 0 31 bytes
                         parsed_result  reg4181 = repeat_cons(BYTE, INF, 0, 31);
                         break;
                     }
        default:
            //printf("ERROR: None matched case expression!");
            return 1;
            break;
    }
    return 0;
};

/*@assigns \nothing; */
int main(int argc, char *argv[])
{
    unsigned int x = run_parser(TAPE, TAPE_LEN);
    if (x == 0) {
        return 0;
        // printf("accepted input.");
    } else {
        // printf("rejected input");
        return 1;
    }
    return 0;
}
