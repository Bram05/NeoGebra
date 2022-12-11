#version 400 core

layout (location = 0) out vec4 colour;

uniform sampler2D u_TextImage;
in vec2 pixelPos;

void main()
{
    vec4 col = texture(u_TextImage, pixelPos);
    colour = col;
}