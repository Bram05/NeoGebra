#version 400 core

layout(location = 0) in vec2 pos;

uniform mat2 u_Mat;

void main()
{
	gl_Position = vec4(u_Mat * pos, 0.0, 1.0);
}