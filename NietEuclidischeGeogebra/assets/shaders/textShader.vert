#version 400 core

layout (location = 0) in vec2 pos;
layout (location = 1) in vec2 texPos;
out vec2 pixelPos;

void main()
{
	pixelPos = texPos;
	gl_Position = vec4(pos, 0.0, 1.0);
}