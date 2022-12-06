#version 400 core

layout(location = 0) in vec2 pos;
layout (location = 1) in vec2 aTexCoord;


out vec2 TexCoords;
	
void main()
{
    TexCoords = aTexCoord;
    gl_Position = vec4(pos, 0.0, 1.0);
}