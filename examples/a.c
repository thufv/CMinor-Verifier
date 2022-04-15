#include<stdio.h>

int main() {
    int i = 0;
    for (; i < 10; ++i) {
        if (i == 1) {
            continue;
        }
    }
}