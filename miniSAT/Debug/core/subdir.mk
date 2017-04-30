################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
CC_SRCS += \
../core/Main.cc \
../core/Solver.cc 

CC_DEPS += \
./core/Main.d \
./core/Solver.d 

OBJS += \
./core/Main.o \
./core/Solver.o 


# Each subdirectory must supply rules for building sources it contributes
core/%.o: ../core/%.cc
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -O0 -g3 -Wall -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


