#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

void printInt(int i) {
    printf("%d\n", i);
}

void printString(char* str) {
    printf("%s\n", str);
}

void error() {
    fprintf(stderr, "runtime error\n");
    exit(EXIT_FAILURE);
}

int readInt() {
    int a;
    scanf("%d", &a);
    getchar();
    return a;
}

char* readString() {
    char *line = NULL;
    size_t len = 0;
    ssize_t lineSize = 0;
    lineSize = getline(&line, &len, stdin);

    if (line[strlen(line) - 1] == '\n') {
        line[strlen(line) - 1] = 0;
    }

    return line;
}

char* concatStrings(char* str1, char* str2) {
    char* line = malloc(strlen(str1) + strlen(str2) + 1);
    int len = 0, size = 1;

    for (int i = 0; i < strlen(str1); ++i) {
        line[len++] = str1[i];
    }
    for (int i = 0; i < strlen(str2); ++i) {
        line[len++] = str2[i];
    }
    line[strlen(str1) + strlen(str2)] = 0;
    
    return line;
}

bool compareStrings(char* str1, char* str2) {
    if (strlen(str1) != strlen(str2)) {
        return false;
    }

    int len = strlen(str1);
    for (int i = 0; i < len; ++i) {
        if (str1[i] != str2[i]) {
            return false;
        }
    }

    return true;
}