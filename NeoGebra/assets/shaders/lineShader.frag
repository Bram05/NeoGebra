#version 400 core

layout(location = 0) out vec4 colour;

uniform vec4 u_Colour;

void main()
{
	colour = u_Colour;
}